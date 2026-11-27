/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Longitudinal.Basic

/-!
# The g-formula at two time points

The g-formula of Robins (1986) for two time points, in the finite setting of
`CausalInference.Longitudinal.Basic`: a finite sample space with a nonnegative mass function,
the time ordering `L0, A0, L1, A1, Y`, with covariates in a finite type `𝓛`.

The core theorem `Longitudinal.gFormula2_eq` is stated for treatment values that may depend on
the covariate history: the value at time `0` is `d0 l0` and the value at time `1` is
`d1 l0 l1`. Taking constant `d0`, `d1` gives static regimes (`Longitudinal.gFormula2_static`);
taking the values prescribed by a dynamic regime gives the dynamic g-formula
(`Longitudinal.gFormula2_dynamic`).

## Main definitions

* `Longitudinal.gFormula2 m L0 A0 L1 A1 d0 d1 Y`: the two time point g-formula functional
  `Σ_{l0, l1} E[Y | L0 = l0, A0 = d0 l0, L1 = l1, A1 = d1 l0 l1]
    · P(L1 = l1 | L0 = l0, A0 = d0 l0) · P(L0 = l0)`.
* `Longitudinal.SeqExchangeable2`: sequential exchangeability at two time points, mean
  independence form, for a target variable `Z` (a potential outcome).
* `Longitudinal.SeqPositive2`: sequential positivity at two time points.
* `Longitudinal.DynamicRegime.first`, `Longitudinal.DynamicRegime.second`: the two decision
  rules of a dynamic regime with two time points.
* `Longitudinal.dynamicOutcome2`: the potential outcome under a dynamic regime, built from the
  static potential outcomes `Ypo a0 a1` and the potential covariate `L1po a0`.

## Main results

* `Longitudinal.gFormula2_eq`: under consistency, sequential exchangeability and sequential
  positivity, `E[Z] = gFormula2`.
* `Longitudinal.gFormula2_static`: `E[Y(a0, a1)]` equals the g-formula.
* `Longitudinal.gFormula2_dynamic`: `E[Y^g]` equals the g-formula with the treatment values
  prescribed by `g`. Consistency of `Y^g` is derived from outcome and covariate consistency.

## Null conditioning events

In `gFormula2`, the term of `(l0, l1)` has a conditional mean and a conditional probability that
are ratios. Under sequential positivity every term whose conditioning event has zero mass also
has a factor `P(L0 = l0) = 0` or `P(L1 = l1 | L0 = l0, A0 = d0 l0) = 0` that is genuinely zero
(a zero numerator over a positive denominator, or a zero mass), so no conclusion depends on the
value given to a ratio with zero denominator.

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), chapters 19 to 21.
-/

@[expose] public section

namespace CausalInference

namespace Longitudinal

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒜 𝓛 : Type*} [DecidableEq 𝒜] [Fintype 𝓛]
  [DecidableEq 𝓛]

/-- The two time point g-formula functional under the mass function `m`, with treatment value
`d0 l0` at time `0` and `d1 l0 l1` at time `1`:
`Σ_{l0, l1} E[Y | L0 = l0, A0 = d0 l0, L1 = l1, A1 = d1 l0 l1]
  · P(L1 = l1 | L0 = l0, A0 = d0 l0) · P(L0 = l0)`. -/
noncomputable def gFormula2 (m : Ω → ℝ) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜) (L1 : Ω → 𝓛) (A1 : Ω → 𝒜)
    (d0 : 𝓛 → 𝒜) (d1 : 𝓛 → 𝓛 → 𝒜) (Y : Ω → ℝ) : ℝ :=
  ∑ l0, ∑ l1,
    condMean m (ev L0 l0 ∩ ev A0 (d0 l0) ∩ ev L1 l1 ∩ ev A1 (d1 l0 l1)) Y *
      condProb m (ev L0 l0 ∩ ev A0 (d0 l0)) (ev L1 l1) * wmass m (ev L0 l0)

/-- Sequential exchangeability at two time points for the target `Z`, in the mean independence
form of `MeanIndepOn`: given `L0 = l0`, `Z` is mean independent of `A0 = d0 l0`; given
`L0 = l0, A0 = d0 l0, L1 = l1`, `Z` is mean independent of `A1 = d1 l0 l1`. -/
def SeqExchangeable2 (m : Ω → ℝ) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜) (L1 : Ω → 𝓛) (A1 : Ω → 𝒜)
    (d0 : 𝓛 → 𝒜) (d1 : 𝓛 → 𝓛 → 𝒜) (Z : Ω → ℝ) : Prop :=
  (∀ l0, MeanIndepOn m (ev L0 l0) (ev A0 (d0 l0)) Z) ∧
    ∀ l0 l1, MeanIndepOn m (ev L0 l0 ∩ ev A0 (d0 l0) ∩ ev L1 l1) (ev A1 (d1 l0 l1)) Z

/-- Sequential positivity at two time points: `P(L0 = l0) > 0` implies
`P(L0 = l0, A0 = d0 l0) > 0`, and `P(L0 = l0, A0 = d0 l0, L1 = l1) > 0` implies
`P(L0 = l0, A0 = d0 l0, L1 = l1, A1 = d1 l0 l1) > 0`. -/
def SeqPositive2 (m : Ω → ℝ) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜) (L1 : Ω → 𝓛) (A1 : Ω → 𝒜)
    (d0 : 𝓛 → 𝒜) (d1 : 𝓛 → 𝓛 → 𝒜) : Prop :=
  (∀ l0, 0 < wmass m (ev L0 l0) → 0 < wmass m (ev L0 l0 ∩ ev A0 (d0 l0))) ∧
    ∀ l0 l1, 0 < wmass m (ev L0 l0 ∩ ev A0 (d0 l0) ∩ ev L1 l1) →
      0 < wmass m (ev L0 l0 ∩ ev A0 (d0 l0) ∩ ev L1 l1 ∩ ev A1 (d1 l0 l1))

/-- **The two time point g-formula** (core form). Let the treatment values be `d0 l0` at time
`0` and `d1 l0 l1` at time `1`. Assume consistency (every sample point following these values
has observed outcome `Y` equal to the target `Z`), sequential exchangeability for `Z` and
sequential positivity. Then the weighted sum of `Z` over the whole space (the mean `E[Z]` when
`m` is a probability mass function) equals the g-formula functional. -/
theorem gFormula2_eq {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω) {L0 : Ω → 𝓛} {A0 : Ω → 𝒜}
    {L1 : Ω → 𝓛} {A1 : Ω → 𝒜} {d0 : 𝓛 → 𝒜} {d1 : 𝓛 → 𝓛 → 𝒜} {Y Z : Ω → ℝ}
    (hcons : ∀ ω, A0 ω = d0 (L0 ω) → A1 ω = d1 (L0 ω) (L1 ω) → Y ω = Z ω)
    (hex : SeqExchangeable2 m L0 A0 L1 A1 d0 d1 Z) (hpos : SeqPositive2 m L0 A0 L1 A1 d0 d1) :
    wsum m univ Z = gFormula2 m L0 A0 L1 A1 d0 d1 Y := by
  rw [wsum_eq_sum_ev univ L0, gFormula2]
  refine sum_congr rfl fun l0 _ => ?_
  rw [univ_inter]
  rcases (wmass_nonneg hm (ev L0 l0)).eq_or_lt with h0 | h0
  · rw [wsum_eq_zero_of_wmass_eq_zero hm h0.symm, ← h0]
    simp
  have h1 := hpos.1 l0 h0
  rw [← wmass_mul_condMean h0.ne', ← (meanIndepOn_iff_condMean_eq hm h1).1 (hex.1 l0),
    condMean_eq_sum_condProb_mul hm h1 L1, mul_sum]
  refine sum_congr rfl fun l1 _ => ?_
  rcases (wmass_nonneg hm (ev L0 l0 ∩ ev A0 (d0 l0) ∩ ev L1 l1)).eq_or_lt with h2 | h2
  · rw [condProb_eq_zero_of_wmass_inter_eq_zero h1 h2.symm]
    ring
  have h3 := hpos.2 l0 l1 h2
  rw [← (meanIndepOn_iff_condMean_eq hm h3).1 (hex.2 l0 l1)]
  have hYZ : condMean m (ev L0 l0 ∩ ev A0 (d0 l0) ∩ ev L1 l1 ∩ ev A1 (d1 l0 l1)) Z =
      condMean m (ev L0 l0 ∩ ev A0 (d0 l0) ∩ ev L1 l1 ∩ ev A1 (d1 l0 l1)) Y := by
    unfold condMean
    congr 1
    refine wsum_congr fun ω hω => ?_
    simp only [mem_inter, mem_ev] at hω
    obtain ⟨⟨⟨hL0, hA0⟩, hL1⟩, hA1⟩ := hω
    exact (hcons ω (by rw [hA0, hL0]) (by rw [hA1, hL0, hL1])).symm
  rw [hYZ]
  ring

/-- **The two time point g-formula for a static regime.** Let `p` be a finite probability
distribution, `Ypo a0 a1` the potential outcome under the static regime `(a0, a1)`, and assume
consistency `A0 = a0, A1 = a1 ⇒ Y = Ypo a0 a1`, sequential exchangeability for `Ypo a0 a1` and
sequential positivity. Then
`E[Y(a0, a1)] = Σ_{l0, l1} E[Y | L0 = l0, A0 = a0, L1 = l1, A1 = a1]
  · P(L1 = l1 | L0 = l0, A0 = a0) · P(L0 = l0)`. -/
theorem gFormula2_static (p : FiniteDist Ω) {L0 : Ω → 𝓛} {A0 : Ω → 𝒜} {L1 : Ω → 𝓛}
    {A1 : Ω → 𝒜} {Y : Ω → ℝ} {Ypo : 𝒜 → 𝒜 → Ω → ℝ} {a0 a1 : 𝒜}
    (hcons : ∀ ω, A0 ω = a0 → A1 ω = a1 → Y ω = Ypo a0 a1 ω)
    (hex : SeqExchangeable2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1) (Ypo a0 a1))
    (hpos : SeqPositive2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1)) :
    p.expect (Ypo a0 a1) =
      ∑ l0, ∑ l1, condMean p (ev L0 l0 ∩ ev A0 a0 ∩ ev L1 l1 ∩ ev A1 a1) Y *
        condProb p (ev L0 l0 ∩ ev A0 a0) (ev L1 l1) * p.prob (ev L0 l0) :=
  gFormula2_eq p.nonneg hcons hex hpos

/-- The decision rule at time `0` of a dynamic regime with two time points, as a function of the
first covariate. -/
def DynamicRegime.first (g : DynamicRegime 2 𝒜 𝓛) (l0 : 𝓛) : 𝒜 :=
  g 0 (fun _ => l0) Fin.elim0

/-- The decision rule at time `1` of a dynamic regime with two time points, as a function of the
two covariates and the first treatment. -/
def DynamicRegime.second (g : DynamicRegime 2 𝒜 𝓛) (l0 l1 : 𝓛) (a0 : 𝒜) : 𝒜 :=
  g 1 ![l0, l1] (fun _ => a0)

/-- The potential outcome under the dynamic regime `g` with two time points. The first
treatment is `a0 = g(L0)`, the potential covariate at time `1` under `a0` is `L1po a0`, the
second treatment is `a1 = g(L0, L1po a0, a0)`, and the outcome is the static potential outcome
`Ypo a0 a1`. The baseline covariate `L0` precedes all treatment and has no potential version;
`L1po a0` depends only on the earlier treatment `a0` by construction. -/
def dynamicOutcome2 (L0 : Ω → 𝓛) (L1po : 𝒜 → Ω → 𝓛) (Ypo : 𝒜 → 𝒜 → Ω → ℝ)
    (g : DynamicRegime 2 𝒜 𝓛) (ω : Ω) : ℝ :=
  Ypo (g.first (L0 ω)) (g.second (L0 ω) (L1po (g.first (L0 ω)) ω) (g.first (L0 ω))) ω

omit [Fintype Ω] [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- Consistency for a dynamic regime follows from outcome and covariate consistency: a sample
point whose observed treatments follow `g` has observed outcome equal to `Y^g`. -/
theorem dynamicOutcome2_consistent {L0 L1 : Ω → 𝓛} {A0 A1 : Ω → 𝒜} {Y : Ω → ℝ}
    {L1po : 𝒜 → Ω → 𝓛} {Ypo : 𝒜 → 𝒜 → Ω → ℝ} (g : DynamicRegime 2 𝒜 𝓛)
    (hY : ∀ ω a0 a1, A0 ω = a0 → A1 ω = a1 → Y ω = Ypo a0 a1 ω)
    (hL : ∀ ω a0, A0 ω = a0 → L1 ω = L1po a0 ω) (ω : Ω)
    (h0 : A0 ω = g.first (L0 ω)) (h1 : A1 ω = g.second (L0 ω) (L1 ω) (g.first (L0 ω))) :
    Y ω = dynamicOutcome2 L0 L1po Ypo g ω := by
  rw [dynamicOutcome2, ← hL ω _ h0]
  exact hY ω _ _ h0 h1

/-- **The two time point g-formula for a dynamic regime.** Assume outcome consistency for every
static regime, covariate consistency at time `1`, sequential exchangeability for `Y^g` with the
treatment values prescribed by `g`, and sequential positivity for those values. Then
`E[Y^g] = Σ_{l0, l1} E[Y | L0 = l0, A0 = g(l0), L1 = l1, A1 = g(l0, l1, g(l0))]
  · P(L1 = l1 | L0 = l0, A0 = g(l0)) · P(L0 = l0)`. -/
theorem gFormula2_dynamic (p : FiniteDist Ω) {L0 L1 : Ω → 𝓛} {A0 A1 : Ω → 𝒜} {Y : Ω → ℝ}
    {L1po : 𝒜 → Ω → 𝓛} {Ypo : 𝒜 → 𝒜 → Ω → ℝ} (g : DynamicRegime 2 𝒜 𝓛)
    (hY : ∀ ω a0 a1, A0 ω = a0 → A1 ω = a1 → Y ω = Ypo a0 a1 ω)
    (hL : ∀ ω a0, A0 ω = a0 → L1 ω = L1po a0 ω)
    (hex : SeqExchangeable2 p L0 A0 L1 A1 g.first (fun l0 l1 => g.second l0 l1 (g.first l0))
      (dynamicOutcome2 L0 L1po Ypo g))
    (hpos : SeqPositive2 p L0 A0 L1 A1 g.first (fun l0 l1 => g.second l0 l1 (g.first l0))) :
    p.expect (dynamicOutcome2 L0 L1po Ypo g) =
      gFormula2 p L0 A0 L1 A1 g.first (fun l0 l1 => g.second l0 l1 (g.first l0)) Y :=
  gFormula2_eq p.nonneg (fun ω h0 h1 => dynamicOutcome2_consistent g hY hL ω h0 h1) hex hpos

end Longitudinal

end CausalInference
