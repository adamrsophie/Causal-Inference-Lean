/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Longitudinal.Basic

/-!
# The finite-horizon g-formula for static regimes

The g-formula of Robins (1986) for any finite number `K` of time points and a static regime,
in the finite setting of `CausalInference.Longitudinal.Basic`, proved by induction on `K`.

## Main definitions

* `Longitudinal.gFormula m A L a Y`: the sum-product form of the g-formula,
  `Σ_{l̄} E[Y | L̄_K = l̄, Ā_K = ā]
    · Π_{t < K} P(L_t = l_t | L̄_{t-1} = l̄_{t-1}, Ā_{t-1} = ā_{t-1})`,
  the sum running over all covariate paths `l̄ : Fin K → 𝓛`.
* `Longitudinal.iceGFormula K m A L a Y`: the recursive (iterated conditional expectation) form.
  With no time points left it is `E[Y]`; otherwise it averages, over the first covariate value
  `l` with weights `P(L_0 = l)`, the same functional of the remaining `K` time points computed
  under the mass function restricted to the event `L_0 = l, A_0 = a_0`. Restricting the mass
  function is conditioning on the history up to normalization, and every ratio in the formula
  is invariant under normalization.

## Main results

* `Longitudinal.gFormula_eq_iceGFormula`: the two forms are equal, for every nonnegative mass
  function, with no hypotheses; the proof matches equal ratios term by term.
* `Longitudinal.condMean_eq_iceGFormula`: under sequential exchangeability (mean independence
  form) and sequential positivity, `E[Z] = iceGFormula K m A L a Z` for every target `Z`. The
  proof is by induction on `K`, generalizing over the mass function: conditioning on the first
  time point produces a model with `K` time points under a restricted mass function, which
  inherits exchangeability and positivity.
* `Longitudinal.Model.expect_Ypo_eq_gFormula`: **the finite-horizon g-formula**. In a
  longitudinal model, under outcome consistency, sequential exchangeability and sequential
  positivity for the static regime `ā`, `E[Y(ā)] = gFormula p A L ā Y`.
* `Longitudinal.Model.expect_Ypo_eq_iceGFormula`: the same identity in the recursive form.

## Null conditioning events

Under sequential positivity, every term of the sum-product form whose final conditioning event
has zero mass contains a genuinely zero factor `P(L_t = l_t | …) = 0`: a zero numerator over a
positive denominator, or a factor whose denominator is zero only after an earlier factor with a
zero numerator. The proof of `condMean_eq_iceGFormula` treats each such case explicitly.

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), part III.
-/

@[expose] public section

namespace CausalInference

namespace Longitudinal

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒜 𝓛 : Type*} [DecidableEq 𝒜] [Fintype 𝓛]
  [DecidableEq 𝓛]

/-- The sum-product form of the g-formula for the static regime `a` under the mass function
`m`: the sum over all covariate paths `l` of `E[Y | L̄_K = l̄, Ā_K = ā]` times the product over
the time points `t` of `P(L_t = l_t | L̄_{t-1} = l̄_{t-1}, Ā_{t-1} = ā_{t-1})`. -/
noncomputable def gFormula {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (a : Fin K → 𝒜) (Y : Ω → ℝ) : ℝ :=
  ∑ l : Fin K → 𝓛, condMean m (hist A L a l K) Y *
    ∏ t : Fin K, condProb m (hist A L a l t) (ev (L t) (l t))

/-- The recursive (iterated conditional expectation) form of the g-formula for the static
regime `a` under the mass function `m`. With no time points it is `E[Y]`. With `K + 1` time
points it is `Σ_l P(L_0 = l) · G_l`, where `G_l` is the recursive form for the remaining `K`
time points under `m` restricted to the event `L_0 = l, A_0 = a_0`. -/
noncomputable def iceGFormula : (K : ℕ) → (Ω → ℝ) → (Fin K → Ω → 𝒜) → (Fin K → Ω → 𝓛) →
    (Fin K → 𝒜) → (Ω → ℝ) → ℝ
  | 0, m, _, _, _, Y => condMean m univ Y
  | K + 1, m, A, L, a, Y => ∑ l, condProb m univ (ev (L 0) l) *
      iceGFormula K (restrict m (ev (L 0) l ∩ ev (A 0) (a 0))) (Fin.tail A) (Fin.tail L)
        (Fin.tail a) Y

/-- The sum-product and the recursive forms of the g-formula are equal, for every mass function
and with no hypotheses: the two expressions consist of the same ratios. -/
theorem gFormula_eq_iceGFormula : ∀ (K : ℕ) (m : Ω → ℝ) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜) (Y : Ω → ℝ),
    gFormula m A L a Y = iceGFormula K m A L a Y
  | 0, m, A, L, a, Y => by simp [gFormula, iceGFormula]
  | K + 1, m, A, L, a, Y => by
    rw [iceGFormula, gFormula, ← (Fin.consEquiv fun _ => 𝓛).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun l0 _ => ?_
    rw [← gFormula_eq_iceGFormula K, gFormula, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, hist_zero,
      Fin.cons_zero, Fin.cons_succ, hist_cons_succ, condMean_restrict, condProb_restrict]
    simp only [Fin.tail]
    ring

omit [Fintype Ω] in
theorem meanIndepOn_restrict {m : Ω → ℝ} (s t u : Finset Ω) (f : Ω → ℝ) :
    MeanIndepOn (restrict m s) t u f ↔ MeanIndepOn m (s ∩ t) u f := by
  simp only [MeanIndepOn, wsum_restrict, wmass_restrict, inter_assoc]

omit [Fintype 𝓛] in
/-- The history event at time `t + 1` including the covariate, for a path starting with `l0`, is
the first time point event intersected with the corresponding event of the shifted model. -/
theorem histL_cons_succ {K : ℕ} (A : Fin (K + 1) → Ω → 𝒜) (L : Fin (K + 1) → Ω → 𝓛)
    (a : Fin (K + 1) → 𝒜) (l0 : 𝓛) (l : Fin K → 𝓛) (t : Fin K) :
    histL A L a (Fin.cons l0 l) t.succ =
      (ev (L 0) l0 ∩ ev (A 0) (a 0)) ∩ histL (Fin.tail A) (Fin.tail L) (Fin.tail a) l t := by
  rw [histL, histL, Fin.val_succ, hist_cons_succ, Fin.cons_succ, inter_assoc]
  rfl

/-- **The recursive g-formula identifies the mean of the target** (core form). For a
nonnegative mass function `m` of positive total mass, a static regime `a` and a target
variable `Z`, if `Z` is mean
independent of `A t = a t` within every history event `L̄_t = l̄_t, Ā_{t-1} = ā_{t-1}`
(sequential exchangeability) and each such event of positive mass keeps positive mass after
adding `A t = a t` (sequential positivity), then `E[Z] = iceGFormula K m A L a Z`. -/
theorem condMean_eq_iceGFormula : ∀ (K : ℕ) {m : Ω → ℝ} (_hm : ∀ ω, 0 ≤ m ω)
    (_hm0 : 0 < wmass m univ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜) (Z : Ω → ℝ)
    (_hex : ∀ (l : Fin K → 𝓛) (t : Fin K), MeanIndepOn m (histL A L a l t) (ev (A t) (a t)) Z)
    (_hpos : ∀ (l : Fin K → 𝓛) (t : Fin K), 0 < wmass m (histL A L a l t) →
      0 < wmass m (histL A L a l t ∩ ev (A t) (a t))),
    condMean m univ Z = iceGFormula K m A L a Z
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | K + 1, m, hm, _, A, L, a, Z, hex, hpos => by
    rw [condMean_eq_sum_condProb_mul hm univ (L 0), iceGFormula]
    refine sum_congr rfl fun l0 _ => ?_
    rw [univ_inter]
    rcases (wmass_nonneg hm (ev (L 0) l0)).eq_or_lt with h0 | h0
    · rw [condProb_eq_zero_of_wmass_inter_eq_zero (by rw [univ_inter]; exact h0.symm)]
      simp
    congr 1
    have hL0 : histL A L a (fun _ => l0) 0 = ev (L 0) l0 := by simp [histL]
    have hH : 0 < wmass m (ev (L 0) l0 ∩ ev (A 0) (a 0)) := by
      have := hpos (fun _ => l0) 0
      rw [hL0] at this
      exact this h0
    have hex0 := hex (fun _ => l0) 0
    rw [hL0] at hex0
    rw [← (meanIndepOn_iff_condMean_eq hm hH).1 hex0,
      show condMean m (ev (L 0) l0 ∩ ev (A 0) (a 0)) Z =
        condMean (restrict m (ev (L 0) l0 ∩ ev (A 0) (a 0))) univ Z by
          rw [condMean_restrict, inter_univ]]
    refine condMean_eq_iceGFormula K (restrict_nonneg hm _)
      (by rw [wmass_restrict, inter_univ]; exact hH) _ _ _ Z (fun l t => ?_) (fun l t => ?_)
    · rw [meanIndepOn_restrict, ← histL_cons_succ]
      exact hex (Fin.cons l0 l) t.succ
    · rw [wmass_restrict, wmass_restrict, ← inter_assoc, ← histL_cons_succ]
      exact hpos (Fin.cons l0 l) t.succ

/-- If two functions agree on every full history event, their g-formulas agree. -/
theorem gFormula_congr {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (a : Fin K → 𝒜) {Y Z : Ω → ℝ} (h : ∀ l, ∀ ω ∈ hist A L a l K, Y ω = Z ω) :
    gFormula m A L a Y = gFormula m A L a Z := by
  refine sum_congr rfl fun l _ => ?_
  rw [condMean, condMean, wsum_congr (h l)]

namespace Model

variable {K : ℕ} (M : Model Ω K 𝒜 𝓛)

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- The mean under the model distribution is the conditional mean given the sure event. -/
theorem expect_eq_condMean (f : Ω → ℝ) : M.p.expect f = condMean M.p univ f := by
  have h1 : wmass M.p univ = 1 := M.p.sum_eq_one
  rw [condMean, h1, div_one]
  rfl

/-- **The finite-horizon g-formula, recursive form.** Under sequential exchangeability and
sequential positivity for the static regime `a`, the mean of the potential outcome `Y(ā)`
equals the recursive g-formula applied to `Y(ā)`; with outcome consistency the recursive
formula may be applied to the observed outcome (`expect_Ypo_eq_gFormula`). -/
theorem expect_Ypo_eq_iceGFormula (a : Fin K → 𝒜) (hex : M.SeqExchangeable a)
    (hpos : M.SeqPositive a) :
    M.p.expect (M.Ypo a) = iceGFormula K M.p M.A M.L a (M.Ypo a) := by
  rw [expect_eq_condMean]
  have h1 : wmass M.p univ = 1 := M.p.sum_eq_one
  exact condMean_eq_iceGFormula K M.p.nonneg (by rw [h1]; exact one_pos) M.A M.L a (M.Ypo a)
    hex hpos

/-- **The finite-horizon g-formula.** In a longitudinal model with `K` time points, assume
outcome consistency, sequential exchangeability (mean independence form) and sequential
positivity for the static regime `a`. Then
`E[Y(ā)] = Σ_{l̄} E[Y | L̄_K = l̄, Ā_K = ā]
  · Π_{t < K} P(L_t = l_t | L̄_{t-1} = l̄_{t-1}, Ā_{t-1} = ā_{t-1})`,
and this equals the recursive form `iceGFormula K p A L a Y`. -/
theorem expect_Ypo_eq_gFormula (a : Fin K → 𝒜) (hcons : M.OutcomeConsistent a)
    (hex : M.SeqExchangeable a) (hpos : M.SeqPositive a) :
    M.p.expect (M.Ypo a) = gFormula M.p M.A M.L a M.Y ∧
      gFormula M.p M.A M.L a M.Y = iceGFormula K M.p M.A M.L a M.Y := by
  refine ⟨?_, gFormula_eq_iceGFormula K _ _ _ _ _⟩
  rw [M.expect_Ypo_eq_iceGFormula a hex hpos, ← gFormula_eq_iceGFormula]
  refine gFormula_congr _ _ _ _ fun l ω hω => (hcons ω fun t => ?_).symm
  simp only [hist, mem_filter, mem_univ, true_and] at hω
  exact (hω t t.isLt).2

end Model

end Longitudinal

end CausalInference
