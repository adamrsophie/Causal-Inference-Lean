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
  `Σ_{l̄} E[Y | L_s = l_s, A_s = a_s for all s < K]
    · Π_{t < K} P(L_t = l_t | L_s = l_s, A_s = a_s for all s < t)`,
  the sum running over all covariate paths `l̄ : Fin K → 𝓛`. The visits are indexed from `0`, so
  the terminal conditioning event fixes the visits `t < K` (the sure event when `K = 0`).
* `Longitudinal.iceGFormula K m A L a Y`: the recursive (iterated conditional expectation) form.
  With no time points left it is `E[Y]`; otherwise it averages, over the first covariate value
  `l` with weights `P(L_0 = l)`, the same functional of the remaining `K` time points computed
  under the mass function restricted to the event `L_0 = l, A_0 = a_0`. Restricting the mass
  function is conditioning on the history up to normalization, and every ratio in the formula
  is invariant under normalization.

## Main results

* `Longitudinal.gFormula_eq_iceGFormula`: the two forms are equal for every mass function, as an
  identity of the totalized expressions (a ratio with zero denominator is read as `0`), proved
  by matching equal ratios term by term. It is not by itself a statement about conditional
  probabilities on null events; its probabilistic reading is `Model.expect_Ypo_eq_gFormula`,
  under sequential positivity.
* `Longitudinal.condMean_eq_iceGFormula`: for a nonnegative mass function of positive total
  mass, under sequential exchangeability (mean independence form) and sequential positivity,
  `E[Z] = iceGFormula K m A L a Z` for every target `Z`. The
  proof is by induction on `K`, generalizing over the mass function: conditioning on the first
  time point produces a model with `K` time points under a restricted mass function, which
  inherits exchangeability and positivity.
* `Longitudinal.Model.expect_Ypo_eq_gFormula`: **the finite-horizon g-formula**. In a
  longitudinal model, under outcome consistency, sequential exchangeability and sequential
  positivity for the static regime `ā`, `E[Y(ā)] = gFormula p A L ā Y`.
* `Longitudinal.Model.expect_Ypo_eq_iceGFormula_obs`: the same identity in the recursive form,
  `E[Y(ā)] = iceGFormula K p A L ā Y` on observed data.
  `Longitudinal.Model.expect_Ypo_eq_iceGFormula` is the intermediate step with the potential
  outcome `Y(ā)` on both sides, needing no consistency.
* `Longitudinal.Model.prob_Ypo_mem_eq_gFormula`: **the distributional g-formula**. Under outcome
  consistency, distributional sequential exchangeability (`Model.SeqExchangeableDist`: mean
  independence for every indicator `1{Y(ā) ∈ B}`) and sequential positivity,
  `P(Y(ā) ∈ B) = gFormula p A L ā 1{Y ∈ B}` for every set `B`. It is the mean g-formula applied
  to indicators (`Model.expect_comp_Ypo_eq_gFormula`).
* `Longitudinal.MeanExchangeabilityExample.not_distributional`: mean exchangeability is not
  enough for the distributional statement. With one time point, a constant covariate and a fair
  treatment, let `Y(1) = 0` for the treated and `Y(1) = ±1` with equal probability for the
  untreated. Consistency, sequential exchangeability in mean form and positivity hold for the
  regime `1`, yet `P(Y(1) = 0) = 1/2` while the g-formula for `1{Y = 0}` is
  `P(Y = 0 | A = 1) = 1`.

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
`m`: the sum over all covariate paths `l` of `E[Y | L_s = l_s, A_s = a_s for all s < K]` times
the product over the time points `t < K` of `P(L_t = l_t | L_s = l_s, A_s = a_s for all s < t)`.
Each factor is a ratio; a ratio with zero denominator is read as `0`, and the identification
theorems carry sequential positivity so that no conclusion rests on that convention. -/
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
and with no hypotheses, as an identity of the totalized expressions: the two consist of the same
ratios, each read as `0` when its denominator vanishes. On a null conditioning event neither side
is a conditional probability, so this is an algebraic identity only; the theorem that interprets
it as a statement about the law of the data is `Model.expect_Ypo_eq_gFormula`, under sequential
positivity. -/
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
  | K + 1, m, hm, hm0, A, L, a, Z, hex, hpos => by
    rw [condMean_eq_sum_condProb_mul hm hm0 (L 0), iceGFormula]
    refine sum_congr rfl fun l0 _ => ?_
    rw [univ_inter]
    rcases (wmass_nonneg hm (ev (L 0) l0)).eq_or_lt with h0 | h0
    · rw [condProb_eq_zero_of_wmass_inter_eq_zero hm0 (by rw [univ_inter]; exact h0.symm)]
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

/-- **The finite-horizon g-formula, recursive form, potential outcome target.** Under sequential
exchangeability and sequential positivity for the static regime `a`, the mean of the potential
outcome `Y(ā)` equals the recursive g-formula applied to `Y(ā)` itself. This is an intermediate
step: the right side still involves `Y(ā)`. The observed-data identity is
`expect_Ypo_eq_iceGFormula_obs`. -/
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
`E[Y(ā)] = Σ_{l̄} E[Y | L_s = l_s, A_s = a_s for all s < K]
  · Π_{t < K} P(L_t = l_t | L_s = l_s, A_s = a_s for all s < t)`,
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

/-- **The finite-horizon g-formula, recursive form, on observed data.** Under outcome
consistency, sequential exchangeability and sequential positivity for the static regime `a`,
`E[Y(ā)] = iceGFormula K p A L ā Y`, the recursive g-formula of the observed outcome. -/
theorem expect_Ypo_eq_iceGFormula_obs (a : Fin K → 𝒜) (hcons : M.OutcomeConsistent a)
    (hex : M.SeqExchangeable a) (hpos : M.SeqPositive a) :
    M.p.expect (M.Ypo a) = iceGFormula K M.p M.A M.L a M.Y :=
  let h := M.expect_Ypo_eq_gFormula a hcons hex hpos
  h.1.trans h.2

/-- **The g-formula for a transformed outcome.** For a function `f : ℝ → ℝ`, under outcome
consistency for `a`, sequential exchangeability in mean form for the target `f ∘ Y(ā)`, and
sequential positivity for `a`, `E[f(Y(ā))] = gFormula p A L ā (f ∘ Y)`. -/
theorem expect_comp_Ypo_eq_gFormula (f : ℝ → ℝ) (a : Fin K → 𝒜) (hcons : M.OutcomeConsistent a)
    (hex : ∀ (l : Fin K → 𝓛) (t : Fin K),
      MeanIndepOn M.p (histL M.A M.L a l t) (ev (M.A t) (a t)) (f ∘ M.Ypo a))
    (hpos : M.SeqPositive a) :
    M.p.expect (f ∘ M.Ypo a) = gFormula M.p M.A M.L a (f ∘ M.Y) :=
  (expect_Ypo_eq_gFormula { M with Y := f ∘ M.Y, Ypo := fun a => f ∘ M.Ypo a } a
    (fun ω h => congrArg f (hcons ω h)) hex hpos).1

/-- Distributional sequential exchangeability for the static regime `a`: for every set `B` of
reals, every time point `t` and every covariate path `l`, within the history event
`L̄_t = l̄_t, Ā_{t-1} = ā_{t-1}` the indicator `1{Y(ā) ∈ B}` is mean independent of the event
`A t = a t` (in the division free form of `MeanIndepOn`). It says that the conditional law of
`Y(ā)` given the history does not change on adding `A t = a t`. It is not implied by the mean
form `Model.SeqExchangeable` (`MeanExchangeabilityExample.not_distributional`). -/
def SeqExchangeableDist (a : Fin K → 𝒜) : Prop :=
  ∀ (B : Set ℝ) (l : Fin K → 𝓛) (t : Fin K),
    MeanIndepOn M.p (histL M.A M.L a l t) (ev (M.A t) (a t)) (B.indicator 1 ∘ M.Ypo a)

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- The probability that a random variable lies in `B` is the mean of its indicator. -/
theorem probOf_mem_eq_expect (Z : Ω → ℝ) (B : Set ℝ) [DecidablePred (· ∈ B)] :
    M.p.probOf (fun ω => Z ω ∈ B) = M.p.expect (B.indicator 1 ∘ Z) := by
  simp [FiniteDist.probOf, FiniteDist.prob, FiniteDist.expect, Set.indicator, sum_filter]

/-- **The distributional g-formula.** In a longitudinal model, under outcome consistency,
distributional sequential exchangeability and sequential positivity for the static regime `a`,
for every set `B` of reals,
`P(Y(ā) ∈ B) = Σ_{l̄} P(Y ∈ B | L_s = l_s, A_s = a_s for all s < K)
  · Π_{t < K} P(L_t = l_t | L_s = l_s, A_s = a_s for all s < t)`,
the g-formula of the observed indicator `1{Y ∈ B}`. Mean exchangeability alone does not suffice
(`MeanExchangeabilityExample.not_distributional`). -/
theorem prob_Ypo_mem_eq_gFormula (a : Fin K → 𝒜) (hcons : M.OutcomeConsistent a)
    (hex : M.SeqExchangeableDist a) (hpos : M.SeqPositive a) (B : Set ℝ)
    [DecidablePred (· ∈ B)] :
    M.p.probOf (fun ω => M.Ypo a ω ∈ B) = gFormula M.p M.A M.L a (B.indicator 1 ∘ M.Y) := by
  rw [probOf_mem_eq_expect]
  exact M.expect_comp_Ypo_eq_gFormula _ a hcons (hex B) hpos

end Model

namespace MeanExchangeabilityExample

/-! ### Mean exchangeability does not give the distributional g-formula -/

/-- The sample space: a point is `(a, n)`, the treatment and a fair coin. -/
abbrev Sample := Bool × Bool

/-- The uniform distribution on the four points: the treatment and the coin are fair and
independent. -/
noncomputable def p : FiniteDist Sample where
  mass _ := 1 / 4
  nonneg _ := by norm_num
  sum_eq_one := by simp

/-- The outcome: `0` for the treated, `1` or `-1` according to the coin for the untreated. -/
noncomputable def Y (ω : Sample) : ℝ := if ω.1 then 0 else if ω.2 then 1 else -1

/-- The model with one time point, a constant covariate, treatment `A = a`, outcome `Y`, and
potential outcome `Y(ā) = Y` under every regime. -/
noncomputable def model : Model Sample 1 Bool Unit where
  p := p
  A _ ω := ω.1
  L _ _ := ()
  Y := Y
  Ypo _ := Y
  Lpo _ _ _ := ()

/-- The regime "treat". -/
def a : Fin 1 → Bool := fun _ => true

/-- Outcome consistency holds for the regime `a`. -/
theorem outcomeConsistent : model.OutcomeConsistent a := fun _ _ => rfl

/-- Sequential exchangeability in mean form holds for `a`: `E[Y(1) | A = 1] = 0 = E[Y(1)]`. -/
theorem seqExchangeable : model.SeqExchangeable a := by
  intro l t
  fin_cases t
  simp only [MeanIndepOn, wsum, wmass, histL, hist, ev, filter_inter, inter_filter, univ_inter,
    filter_filter, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [model, a, p, Y]

/-- Sequential positivity holds for `a`. -/
theorem seqPositive : model.SeqPositive a := by
  intro l t _
  fin_cases t
  simp only [wmass, histL, hist, ev, filter_inter, inter_filter, univ_inter,
    filter_filter, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [model, a, p]

/-- `P(Y(1) = 0) = 1/2`. -/
theorem prob_Ypo_eq_zero :
    model.p.probOf (fun ω => model.Ypo a ω ∈ ({0} : Set ℝ)) = 1 / 2 := by
  simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num [model, Y, p]

/-- The g-formula of the observed indicator `1{Y = 0}` is `P(Y = 0 | A = 1) = 1`. -/
theorem gFormula_indicator :
    gFormula model.p model.A model.L a (({0} : Set ℝ).indicator 1 ∘ model.Y) = 1 := by
  rw [gFormula_eq_iceGFormula]
  simp only [iceGFormula, condProb, condMean, wmass, wsum, restrict, ev, filter_inter,
    inter_filter, univ_inter, filter_filter, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.sum_unique]
  norm_num [model, a, p, Y, Set.indicator, Pi.single_apply]

/-- **Mean exchangeability does not suffice for the distributional g-formula.** In this model
outcome consistency, sequential exchangeability in mean form and sequential positivity hold for
the regime `a`, but `P(Y(1) = 0) = 1/2` while the g-formula of `1{Y = 0}` is `1`; in particular
distributional sequential exchangeability fails. -/
theorem not_distributional :
    model.OutcomeConsistent a ∧ model.SeqExchangeable a ∧ model.SeqPositive a ∧
      model.p.probOf (fun ω => model.Ypo a ω ∈ ({0} : Set ℝ)) = 1 / 2 ∧
      gFormula model.p model.A model.L a (({0} : Set ℝ).indicator 1 ∘ model.Y) = 1 ∧
      ¬ model.SeqExchangeableDist a := by
  refine ⟨outcomeConsistent, seqExchangeable, seqPositive, prob_Ypo_eq_zero, gFormula_indicator,
    fun h => ?_⟩
  have := model.prob_Ypo_mem_eq_gFormula a outcomeConsistent h seqPositive {0}
  rw [prob_Ypo_eq_zero, gFormula_indicator] at this
  norm_num at this

end MeanExchangeabilityExample

end Longitudinal

end CausalInference
