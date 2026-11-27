/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Basic.FiniteDistribution

/-!
# Longitudinal causal inference: finite setting, histories and regimes

The basic objects of longitudinal causal inference in the sense of Robins (1986), in a finite
setting: a finite sample space `Ω` carrying a nonnegative mass function, finitely many time
points, treatments and covariates with values in finite types. Every conditional probability
and conditional mean is conditioning on an event; such a quantity is a ratio, and every theorem
that uses one has an explicit positivity hypothesis making the denominator positive wherever
the ratio matters. Nothing here is a general measurable-space statement.

## Weighted sums on a finite sample space

The core lemmas work with an arbitrary nonnegative mass function `m : Ω → ℝ` (not necessarily
summing to one), so that restricting `m` to an event (`Longitudinal.restrict`) stays inside the
same theory. This is what makes induction over time points possible: conditioning on the first
time point is restriction of the mass function, and conditional probabilities are invariant
under the missing normalization.

* `Longitudinal.wmass m s`: the mass of the event `s`.
* `Longitudinal.wsum m s f`: the sum of `m · f` over `s` (the partial expectation `E[1_s f]`).
* `Longitudinal.condMean m s f`: the conditional mean `E[f | s] = E[1_s f] / P(s)`.
* `Longitudinal.condProb m s t`: the conditional probability `P(t | s) = P(s ∩ t) / P(s)`.
* `Longitudinal.ev X x`: the event `{X = x}`.
* `Longitudinal.MeanIndepOn m s t f`: within the event `s`, the variable `f` is mean independent
  of the event `t`, in the division free form `E[1_{s ∩ t} f] P(s) = E[1_s f] P(s ∩ t)`. When
  `P(s ∩ t) > 0` this says exactly `E[f | s ∩ t] = E[f | s]`
  (`Longitudinal.meanIndepOn_iff_condMean_eq`); when `P(s ∩ t) = 0` it holds trivially.

## Longitudinal models

* `Longitudinal.Model Ω K 𝒜 𝓛`: a finite probability distribution on `Ω`, treatments
  `A t` and covariates `L t` at the time points `t : Fin K` (at time `t` the covariate `L t` is
  measured before the treatment `A t`), an observed outcome `Y` after the last time point,
  potential outcomes `Ypo ā` and potential covariates `Lpo ā t` for every static regime `ā`.
* `Model.Nonanticipating`: the potential covariate at time `t` depends only on the treatments
  strictly before `t`.
* `Model.OutcomeConsistent`, `Model.CovariateConsistent`, `Model.Consistent`: consistency is an
  explicit hypothesis, not built into the construction.
* `Longitudinal.hist A L ā l̄ t`: the history event `L̄_{t-1} = l̄_{t-1}, Ā_{t-1} = ā_{t-1}`
  (the first `t` time points follow the covariate path `l̄` and the regime `ā`).
* `Longitudinal.histL A L ā l̄ t`: the history event at time `t` including the covariate at `t`.
* `Model.SeqExchangeable ā`: sequential exchangeability for the static regime `ā`, in the mean
  independence form: for every time `t` and history, `Ypo ā` is mean independent of the event
  `A t = ā t` given `L̄_t = l̄_t, Ā_{t-1} = ā_{t-1}`.
* `Model.SeqPositive ā`: sequential positivity for `ā`.
* `Longitudinal.DynamicRegime K 𝒜 𝓛`: a rule assigning a treatment at time `t` from the
  covariate history up to `t` and the treatment history before `t`.

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period: application to control of the healthy worker survivor effect*, Mathematical
  Modelling 7 (1986).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman and Hall/CRC (2020),
  part III.
-/

@[expose] public section

namespace CausalInference

namespace Longitudinal

open Finset

section Weighted

variable {Ω : Type*}

/-- The mass of the event `s` under the mass function `m`. -/
def wmass (m : Ω → ℝ) (s : Finset Ω) : ℝ := ∑ ω ∈ s, m ω

/-- The weighted sum of `f` over the event `s`: the partial expectation `E[1_s f]` under `m`. -/
def wsum (m : Ω → ℝ) (s : Finset Ω) (f : Ω → ℝ) : ℝ := ∑ ω ∈ s, m ω * f ω

/-- The conditional mean `E[f | s] = E[1_s f] / P(s)` under `m`. It is meaningful only when
`P(s) > 0`; every theorem using it supplies that hypothesis where it matters. -/
noncomputable def condMean (m : Ω → ℝ) (s : Finset Ω) (f : Ω → ℝ) : ℝ :=
  wsum m s f / wmass m s

/-- The conditional probability `P(t | s) = P(s ∩ t) / P(s)` under `m`. It is meaningful only
when `P(s) > 0`. -/
noncomputable def condProb [DecidableEq Ω] (m : Ω → ℝ) (s t : Finset Ω) : ℝ :=
  wmass m (s ∩ t) / wmass m s

/-- The event `{X = x}`. -/
def ev [Fintype Ω] {α : Type*} [DecidableEq α] (X : Ω → α) (x : α) : Finset Ω :=
  univ.filter fun ω => X ω = x

@[simp] theorem mem_ev [Fintype Ω] {α : Type*} [DecidableEq α] {X : Ω → α} {x : α}
    {ω : Ω} :
    ω ∈ ev X x ↔ X ω = x := by
  simp [ev]

/-- The restriction of the mass function `m` to the event `s`: the mass is kept on `s` and set
to zero off `s`. Conditioning on `s` is restriction followed by normalization. -/
def restrict [DecidableEq Ω] (m : Ω → ℝ) (s : Finset Ω) : Ω → ℝ :=
  fun ω => if ω ∈ s then m ω else 0

/-- Within the event `s`, the variable `f` is mean independent of the event `t`, stated without
division: `E[1_{s ∩ t} f] P(s) = E[1_s f] P(s ∩ t)`. If `P(s ∩ t) > 0` this is the equality of
conditional means `E[f | s ∩ t] = E[f | s]` (`meanIndepOn_iff_condMean_eq`); if `P(s ∩ t) = 0`
both sides vanish and the condition is empty. -/
def MeanIndepOn [DecidableEq Ω] (m : Ω → ℝ) (s t : Finset Ω) (f : Ω → ℝ) : Prop :=
  wsum m (s ∩ t) f * wmass m s = wsum m s f * wmass m (s ∩ t)

variable {m : Ω → ℝ}

theorem wmass_nonneg (hm : ∀ ω, 0 ≤ m ω) (s : Finset Ω) : 0 ≤ wmass m s :=
  sum_nonneg fun ω _ => hm ω

theorem wmass_mono (hm : ∀ ω, 0 ≤ m ω) {s t : Finset Ω} (h : s ⊆ t) :
    wmass m s ≤ wmass m t :=
  sum_le_sum_of_subset_of_nonneg h fun ω _ _ => hm ω

/-- On an event of zero mass every weighted sum vanishes. -/
theorem wsum_eq_zero_of_wmass_eq_zero (hm : ∀ ω, 0 ≤ m ω) {s : Finset Ω} (h : wmass m s = 0)
    (f : Ω → ℝ) : wsum m s f = 0 := by
  have h0 := (sum_eq_zero_iff_of_nonneg fun ω _ => hm ω).1 h
  exact sum_eq_zero fun ω hω => by rw [h0 ω hω, zero_mul]

/-- A conditional probability given an event of zero mass in its intersection vanishes. -/
theorem condProb_eq_zero_of_wmass_inter_eq_zero [DecidableEq Ω] {s t : Finset Ω}
    (h : wmass m (s ∩ t) = 0) :
    condProb m s t = 0 := by
  rw [condProb, h, zero_div]

theorem condProb_nonneg [DecidableEq Ω] (hm : ∀ ω, 0 ≤ m ω) (s t : Finset Ω) :
    0 ≤ condProb m s t :=
  div_nonneg (wmass_nonneg hm _) (wmass_nonneg hm _)

/-- Weighted sums agree on an event where the two functions agree. -/
theorem wsum_congr {s : Finset Ω} {f g : Ω → ℝ} (h : ∀ ω ∈ s, f ω = g ω) :
    wsum m s f = wsum m s g :=
  sum_congr rfl fun ω hω => by rw [h ω hω]

/-- The weighted sum of a constant. -/
theorem wsum_const (s : Finset Ω) (c : ℝ) : wsum m s (fun _ => c) = wmass m s * c := by
  simp [wsum, wmass, sum_mul]

/-- The mean of a function given an event of positive mass, times that mass, is the weighted
sum. -/
theorem wmass_mul_condMean {s : Finset Ω} (h : wmass m s ≠ 0) (f : Ω → ℝ) :
    wmass m s * condMean m s f = wsum m s f := by
  rw [condMean]; field_simp

/-- Partition of a weighted sum by the values of a finite-valued variable. -/
theorem wsum_eq_sum_ev [Fintype Ω] [DecidableEq Ω] {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset Ω) (X : Ω → α) (f : Ω → ℝ) :
    wsum m s f = ∑ x, wsum m (s ∩ ev X x) f := by
  unfold wsum
  rw [← sum_fiberwise s X (fun ω => m ω * f ω)]
  refine sum_congr rfl fun x _ => sum_congr ?_ fun _ _ => rfl
  ext ω; simp

/-- Partition of a mass by the values of a finite-valued variable. -/
theorem wmass_eq_sum_ev [Fintype Ω] [DecidableEq Ω] {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset Ω) (X : Ω → α) :
    wmass m s = ∑ x, wmass m (s ∩ ev X x) := by
  have h := wsum_eq_sum_ev (m := m) s X (fun _ => 1)
  simpa [wsum_const] using h

/-- The law of total expectation for a finite-valued variable `X` given an event `s`:
`E[f | s] = Σ_x P(X = x | s) E[f | s, X = x]`. Terms whose conditioning event `s ∩ {X = x}` has
zero mass carry the weight `P(X = x | s) = 0`, a zero numerator. The identity is meaningful when
`P(s) > 0`; if `P(s) = 0` both sides are the conventional value `0`, and every use of this lemma
in the library is under the hypothesis `P(s) > 0`. -/
theorem condMean_eq_sum_condProb_mul [Fintype Ω] [DecidableEq Ω] (hm : ∀ ω, 0 ≤ m ω)
    {α : Type*} [Fintype α] [DecidableEq α] (s : Finset Ω) (X : Ω → α) (f : Ω → ℝ) :
    condMean m s f = ∑ x, condProb m s (ev X x) * condMean m (s ∩ ev X x) f := by
  rw [condMean, wsum_eq_sum_ev s X, sum_div]
  refine sum_congr rfl fun x _ => ?_
  by_cases h : wmass m (s ∩ ev X x) = 0
  · rw [wsum_eq_zero_of_wmass_eq_zero hm h, condProb_eq_zero_of_wmass_inter_eq_zero h]
    simp
  · rw [condProb, condMean]
    field_simp

/-- The cross multiplied mean independence is equality of conditional means when the smaller
event has positive mass. -/
theorem meanIndepOn_iff_condMean_eq [DecidableEq Ω] (hm : ∀ ω, 0 ≤ m ω) {s t : Finset Ω}
    {f : Ω → ℝ} (hpos : 0 < wmass m (s ∩ t)) :
    MeanIndepOn m s t f ↔ condMean m (s ∩ t) f = condMean m s f := by
  have hs : 0 < wmass m s := hpos.trans_le (wmass_mono hm inter_subset_left)
  rw [MeanIndepOn, condMean, condMean, div_eq_div_iff hpos.ne' hs.ne']

/-- Restriction of the mass function: masses of events. -/
theorem wmass_restrict [DecidableEq Ω] (s t : Finset Ω) :
    wmass (restrict m s) t = wmass m (s ∩ t) := by
  simp [wmass, restrict, sum_ite_mem, inter_comm]

/-- Restriction of the mass function: weighted sums. -/
theorem wsum_restrict [DecidableEq Ω] (s t : Finset Ω) (f : Ω → ℝ) :
    wsum (restrict m s) t f = wsum m (s ∩ t) f := by
  simp [wsum, restrict, ite_mul, sum_ite_mem, inter_comm]

theorem restrict_nonneg [DecidableEq Ω] (hm : ∀ ω, 0 ≤ m ω) (s : Finset Ω) (ω : Ω) :
    0 ≤ restrict m s ω := by
  unfold restrict; split_ifs <;> simp [hm ω]

theorem condMean_restrict [DecidableEq Ω] (s t : Finset Ω) (f : Ω → ℝ) :
    condMean (restrict m s) t f = condMean m (s ∩ t) f := by
  rw [condMean, condMean, wsum_restrict, wmass_restrict]

theorem condProb_restrict [DecidableEq Ω] (s t u : Finset Ω) :
    condProb (restrict m s) t u = condProb m (s ∩ t) u := by
  rw [condProb, condProb, wmass_restrict, wmass_restrict, inter_assoc]

end Weighted

section Model

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒜 𝓛 : Type*} [DecidableEq 𝒜] [DecidableEq 𝓛]

/-- The history event at time `t` (a natural number, at most the number `K` of time points) for
the treatment path `a` and the covariate path `l`: for every time point `s < t`, the covariate
`L s` equals `l s` and the treatment `A s` equals `a s`. At `t = 0` it is the sure event, at
`t = K` it fixes the whole observed history. -/
def hist {K : ℕ} (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜) (l : Fin K → 𝓛)
    (t : ℕ) : Finset Ω :=
  univ.filter fun ω => ∀ s : Fin K, (s : ℕ) < t → L s ω = l s ∧ A s ω = a s

/-- The history event at the time point `t` including the covariate measured at `t`:
`L̄_t = l̄_t, Ā_{t-1} = ā_{t-1}`. This is the conditioning event of sequential exchangeability
at time `t`. -/
def histL {K : ℕ} (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜) (l : Fin K → 𝓛)
    (t : Fin K) : Finset Ω :=
  hist A L a l t ∩ ev (L t) (l t)

omit [DecidableEq Ω] in
@[simp] theorem hist_zero {K : ℕ} (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜)
    (l : Fin K → 𝓛) : hist A L a l 0 = univ := by
  ext ω; simp [hist]

/-- The history event of a path starting with `l0`, after `t + 1` time points, is the first
time point event `L 0 = l0, A 0 = a 0` intersected with the history event of the shifted model
after `t` time points. -/
theorem hist_cons_succ {K : ℕ} (A : Fin (K + 1) → Ω → 𝒜) (L : Fin (K + 1) → Ω → 𝓛)
    (a : Fin (K + 1) → 𝒜) (l0 : 𝓛) (l : Fin K → 𝓛) (t : ℕ) :
    hist A L a (Fin.cons l0 l) (t + 1) =
      (ev (L 0) l0 ∩ ev (A 0) (a 0)) ∩ hist (Fin.tail A) (Fin.tail L) (Fin.tail a) l t := by
  ext ω
  simp only [hist, mem_filter, mem_univ, true_and, mem_inter, mem_ev]
  simp [Fin.forall_fin_succ, Fin.tail, and_assoc]

/-- A longitudinal model with `K` time points on the finite sample space `Ω`. At each time
point `t : Fin K` the covariate `L t` (values in `𝓛`) is measured and then the treatment `A t`
(values in `𝒜`) is assigned; the outcome `Y` is measured after the last time point. For every
static regime, that is a treatment sequence `a : Fin K → 𝒜`, the model carries the potential
outcome `Ypo a` and the potential covariates `Lpo a t`. Consistency and the dependence of
`Lpo a t` on earlier treatments only are not built in; they are the explicit hypotheses
`Model.Consistent` and `Model.Nonanticipating`. -/
structure Model (Ω : Type*) [Fintype Ω] (K : ℕ) (𝒜 𝓛 : Type*) where
  /-- The distribution of the sample point. -/
  p : FiniteDist Ω
  /-- The observed treatment at each time point. -/
  A : Fin K → Ω → 𝒜
  /-- The observed covariate at each time point (measured before the treatment). -/
  L : Fin K → Ω → 𝓛
  /-- The observed outcome after the last time point. -/
  Y : Ω → ℝ
  /-- The potential outcome under the static regime `a`. -/
  Ypo : (Fin K → 𝒜) → Ω → ℝ
  /-- The potential covariate at time `t` under the static regime `a`. -/
  Lpo : (Fin K → 𝒜) → Fin K → Ω → 𝓛

namespace Model

variable {K : ℕ} (M : Model Ω K 𝒜 𝓛)

/-- The potential covariate at time `t` depends only on the treatments strictly before `t`. -/
def Nonanticipating : Prop :=
  ∀ (a a' : Fin K → 𝒜) (t : Fin K), (∀ s : Fin K, s < t → a s = a' s) → M.Lpo a t = M.Lpo a' t

/-- Outcome consistency for the static regime `a`: a sample point whose observed treatments
follow `a` at every time point has observed outcome equal to the potential outcome `Ypo a`. -/
def OutcomeConsistent (a : Fin K → 𝒜) : Prop :=
  ∀ ω, (∀ t, M.A t ω = a t) → M.Y ω = M.Ypo a ω

/-- Covariate consistency: a sample point whose observed treatments before `t` follow `a` has
observed covariate at `t` equal to the potential covariate `Lpo a t`. -/
def CovariateConsistent : Prop :=
  ∀ (a : Fin K → 𝒜) ω (t : Fin K), (∀ s : Fin K, s < t → M.A s ω = a s) → M.L t ω = M.Lpo a t ω

/-- Consistency of outcomes for every static regime and of covariates. -/
def Consistent : Prop :=
  (∀ a, M.OutcomeConsistent a) ∧ M.CovariateConsistent

/-- Sequential exchangeability for the static regime `a`, in the mean independence form: for
every time point `t` and every covariate path `l`, within the history event
`L̄_t = l̄_t, Ā_{t-1} = ā_{t-1}` the potential outcome `Ypo a` is mean independent of the event
`A t = a t` (in the division free form of `MeanIndepOn`). This is weaker than full conditional
independence `Y(ā) ⫫ A_t | L̄_t, Ā_{t-1} = ā_{t-1}`. -/
def SeqExchangeable (a : Fin K → 𝒜) : Prop :=
  ∀ (l : Fin K → 𝓛) (t : Fin K),
    MeanIndepOn M.p (histL M.A M.L a l t) (ev (M.A t) (a t)) (M.Ypo a)

/-- Sequential positivity for the static regime `a`: every history event
`L̄_t = l̄_t, Ā_{t-1} = ā_{t-1}` of positive probability keeps positive probability after adding
`A t = a t`. -/
def SeqPositive (a : Fin K → 𝒜) : Prop :=
  ∀ (l : Fin K → 𝓛) (t : Fin K), 0 < wmass M.p (histL M.A M.L a l t) →
    0 < wmass M.p (histL M.A M.L a l t ∩ ev (M.A t) (a t))

end Model

end Model

/-- A dynamic treatment regime with `K` time points: at time `t` it assigns a treatment as a
function of the covariate history `L_0, …, L_t` and of the treatment history `A_0, …, A_{t-1}`.
-/
def DynamicRegime (K : ℕ) (𝒜 𝓛 : Type*) : Type _ :=
  (t : Fin K) → (Fin (t + 1) → 𝓛) → (Fin t → 𝒜) → 𝒜

/-- The static regime `a` seen as a dynamic regime that ignores the history. -/
def DynamicRegime.ofStatic {K : ℕ} {𝒜 𝓛 : Type*} (a : Fin K → 𝒜) : DynamicRegime K 𝒜 𝓛 :=
  fun t _ _ => a t

end Longitudinal

end CausalInference
