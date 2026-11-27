/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Longitudinal.GFormula
public import CausalInference.Longitudinal.Weighting

/-!
# Bridge between the general-horizon and the two time point g-formulas

The library has two formalizations of the g-formula of Robins (1986) in the finite setting of
`CausalInference.Longitudinal.Basic`: the general-horizon form of `GFormula.lean`, stated for a
`Longitudinal.Model` with `K` time points and normalized (a conditional mean given the sure
event), and the two time point form of `TwoTime.lean`, stated for loose random variables
`L0, A0, L1, A1` and unnormalized (a weighted sum over the sample space). This file proves that
they agree at horizon `2` and translates between the two kinds of model.

## Main results

* `Longitudinal.gFormula2_eq_wmass_mul_gFormula`: for a nonnegative mass function `m`,
  `gFormula2 = wmass m univ * gFormula` at horizon `2` for a static regime;
  `Longitudinal.gFormula_two_eq_gFormula2`: the two are equal for a probability distribution.
* `Longitudinal.Model.seqExchangeable_iff_two`, `Longitudinal.Model.seqPositive_iff_two`,
  `Longitudinal.Model.outcomeConsistent_iff_two`: the assumptions of `GFormula.lean` at two time
  points are the assumptions of `TwoTime.lean`.
* `Longitudinal.Model.expect_Ypo_eq_gFormula2`: on a model with two time points, `E[Y(ā)]`
  equals both forms of the g-formula.
* `Longitudinal.Model.ofTwoTime`: the two time point data as a `Model`, with
  `Longitudinal.Model.ofTwoTime_nonanticipating`,
  `Longitudinal.Model.ofTwoTime_covariateConsistent_iff` and
  `Longitudinal.Model.ofTwoTime_outcomeConsistent_iff`.
* `Longitudinal.ipw2_eq_gFormula2_static`: the two time point weighted mean `ipw2` equals
  `gFormula2` as an identity of finite sums, with no hypothesis (a public restatement of the
  identity behind `ipw2_static`).

The dynamic regime form of the bridge is `Longitudinal.gFormula2_eq_wmass_mul_gFormulaDyn` in
`CausalInference.Longitudinal.Dynamic`, since it needs the general-horizon dynamic g-formula.

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), chapters 19 and 21.
-/

@[expose] public section

namespace CausalInference

namespace Longitudinal

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒜 𝓛 : Type*} [DecidableEq 𝒜] [Fintype 𝓛]
  [DecidableEq 𝓛]

omit [Fintype Ω] in
/-- Restricting a mass function twice is restricting it to the intersection. -/
theorem restrict_restrict (m : Ω → ℝ) (s t : Finset Ω) :
    restrict (restrict m s) t = restrict m (s ∩ t) := by
  funext ω
  by_cases hs : ω ∈ s <;> by_cases ht : ω ∈ t <;> simp [restrict, hs, ht]

/-- **The general-horizon g-formula at two time points is the two time point g-formula.** For
a nonnegative mass function `m`, treatments `A 0, A 1`, covariates `L 0, L 1` and a static
regime `a`, the unnormalized two time point functional `gFormula2` equals the total mass times
the normalized `gFormula` at horizon `2`. For a probability mass function the two agree. -/
theorem gFormula2_eq_wmass_mul_gFormula {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω) (A : Fin 2 → Ω → 𝒜)
    (L : Fin 2 → Ω → 𝓛) (a : Fin 2 → 𝒜) (Y : Ω → ℝ) :
    gFormula2 m (L 0) (A 0) (L 1) (A 1) (fun _ => a 0) (fun _ _ => a 1) Y =
      wmass m univ * gFormula m A L a Y := by
  rw [gFormula_eq_iceGFormula, iceGFormula, gFormula2, mul_sum]
  refine sum_congr rfl fun l0 _ => ?_
  simp only [iceGFormula, condProb_restrict, condMean_restrict, restrict_restrict, mul_sum]
  refine sum_congr rfl fun l1 _ => ?_
  have h1 : (Fin.succ (0 : Fin 1)) = (1 : Fin 2) := rfl
  simp only [Fin.tail, h1, inter_univ, inter_assoc]
  have hL0 : wmass m univ * condProb m univ (ev (L 0) l0) = wmass m (ev (L 0) l0) := by
    rw [condProb, univ_inter]
    rcases (wmass_nonneg hm univ).eq_or_lt with h | h
    · rw [← h, zero_mul]
      exact le_antisymm (wmass_nonneg hm _) (h ▸ wmass_mono hm (subset_univ _))
    · field_simp
  rw [← mul_assoc, hL0]
  ring

/-- For a finite probability distribution the general-horizon g-formula at two time points
equals the two time point g-formula `gFormula2` for the static regime `(a 0, a 1)`. -/
theorem gFormula_two_eq_gFormula2 (p : FiniteDist Ω) (A : Fin 2 → Ω → 𝒜) (L : Fin 2 → Ω → 𝓛)
    (a : Fin 2 → 𝒜) (Y : Ω → ℝ) :
    gFormula p A L a Y =
      gFormula2 p (L 0) (A 0) (L 1) (A 1) (fun _ => a 0) (fun _ _ => a 1) Y := by
  have h1 : wmass p univ = 1 := p.sum_eq_one
  rw [gFormula2_eq_wmass_mul_gFormula p.nonneg, h1, one_mul]

omit [Fintype 𝓛] in
/-- At two time points, the history event at time `0` including the covariate is `L 0 = l 0`. -/
theorem histL_two_zero (A : Fin 2 → Ω → 𝒜) (L : Fin 2 → Ω → 𝓛) (a : Fin 2 → 𝒜)
    (l : Fin 2 → 𝓛) : histL A L a l 0 = ev (L 0) (l 0) := by
  simp [histL]

omit [Fintype 𝓛] in
/-- At two time points, the history event at time `1` including the covariate is
`L 0 = l 0, A 0 = a 0, L 1 = l 1`. -/
theorem histL_two_one (A : Fin 2 → Ω → 𝒜) (L : Fin 2 → Ω → 𝓛) (a : Fin 2 → 𝒜)
    (l : Fin 2 → 𝓛) :
    histL A L a l 1 = ev (L 0) (l 0) ∩ ev (A 0) (a 0) ∩ ev (L 1) (l 1) := by
  ext ω
  simp [histL, hist, and_assoc]

namespace Model

variable (M : Model Ω 2 𝒜 𝓛)

omit [Fintype 𝓛] in
/-- **Translation of sequential exchangeability.** For a longitudinal model with two time points,
sequential exchangeability for the static regime `a` (`Model.SeqExchangeable`) is the two time
point condition `SeqExchangeable2` for the potential outcome `Ypo a`, with the constant
treatment values `a 0` and `a 1`. -/
theorem seqExchangeable_iff_two (a : Fin 2 → 𝒜) :
    M.SeqExchangeable a ↔ SeqExchangeable2 M.p (M.L 0) (M.A 0) (M.L 1) (M.A 1)
      (fun _ => a 0) (fun _ _ => a 1) (M.Ypo a) := by
  constructor
  · intro h
    refine ⟨fun l0 => ?_, fun l0 l1 => ?_⟩
    · have := h ![l0, l0] 0
      rwa [histL_two_zero] at this
    · have := h ![l0, l1] 1
      rwa [histL_two_one] at this
  · rintro ⟨h0, h1⟩ l t
    fin_cases t
    · simpa [histL_two_zero] using h0 (l 0)
    · simpa [histL_two_one] using h1 (l 0) (l 1)

omit [Fintype 𝓛] in
/-- **Translation of sequential positivity.** For a longitudinal model with two time points,
sequential positivity for the static regime `a` is the two time point condition
`SeqPositive2` with the constant treatment values `a 0` and `a 1`. -/
theorem seqPositive_iff_two (a : Fin 2 → 𝒜) :
    M.SeqPositive a ↔ SeqPositive2 M.p (M.L 0) (M.A 0) (M.L 1) (M.A 1)
      (fun _ => a 0) (fun _ _ => a 1) := by
  constructor
  · intro h
    refine ⟨fun l0 => ?_, fun l0 l1 => ?_⟩
    · have := h ![l0, l0] 0
      rwa [histL_two_zero] at this
    · have := h ![l0, l1] 1
      rwa [histL_two_one] at this
  · rintro ⟨h0, h1⟩ l t
    fin_cases t
    · simpa [histL_two_zero] using h0 (l 0)
    · simpa [histL_two_one] using h1 (l 0) (l 1)

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- **Translation of outcome consistency.** At two time points, outcome consistency for the
static regime `a` says that `A 0 = a 0` and `A 1 = a 1` imply `Y = Ypo a`. -/
theorem outcomeConsistent_iff_two (a : Fin 2 → 𝒜) :
    M.OutcomeConsistent a ↔
      ∀ ω, M.A 0 ω = a 0 → M.A 1 ω = a 1 → M.Y ω = M.Ypo a ω := by
  refine ⟨fun h ω h0 h1 => h ω (Fin.forall_fin_two.2 ⟨h0, h1⟩), fun h ω ht => h ω (ht 0) (ht 1)⟩

/-- **The two forms of the two time point g-formula agree on a model.** In a longitudinal model
with two time points, under outcome consistency, sequential exchangeability and sequential
positivity for the static regime `a`, the mean `E[Y(a)]` equals both the general-horizon
`gFormula` and the two time point `gFormula2`; the second identity is also obtained from
`gFormula2_static` through the translations above. -/
theorem expect_Ypo_eq_gFormula2 (a : Fin 2 → 𝒜) (hcons : M.OutcomeConsistent a)
    (hex : M.SeqExchangeable a) (hpos : M.SeqPositive a) :
    M.p.expect (M.Ypo a) = gFormula M.p M.A M.L a M.Y ∧
      M.p.expect (M.Ypo a) = gFormula2 M.p (M.L 0) (M.A 0) (M.L 1) (M.A 1)
        (fun _ => a 0) (fun _ _ => a 1) M.Y := by
  refine ⟨(M.expect_Ypo_eq_gFormula a hcons hex hpos).1, ?_⟩
  exact gFormula2_static M.p (Ypo := fun _ _ => M.Ypo a)
    ((M.outcomeConsistent_iff_two a).1 hcons) ((M.seqExchangeable_iff_two a).1 hex)
    ((M.seqPositive_iff_two a).1 hpos)

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- **Translation from the two time point data to a model.** The data of the two time point
setting (a distribution `p`, covariates `L0`, `L1`, treatments `A0`, `A1`, an outcome `Y`, static
potential outcomes `Ypo a0 a1`, and a potential covariate `L1po a0` at time `1`) form a
longitudinal model with two time points. The baseline covariate `L0` precedes all treatment, so
its potential version is `L0` itself under every regime. -/
def ofTwoTime (p : FiniteDist Ω) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜) (L1 : Ω → 𝓛) (A1 : Ω → 𝒜)
    (Y : Ω → ℝ) (Ypo : 𝒜 → 𝒜 → Ω → ℝ) (L1po : 𝒜 → Ω → 𝓛) : Model Ω 2 𝒜 𝓛 where
  p := p
  A := ![A0, A1]
  L := ![L0, L1]
  Y := Y
  Ypo a := Ypo (a 0) (a 1)
  Lpo a := ![L0, L1po (a 0)]

section OfTwoTime

variable (p : FiniteDist Ω) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜) (L1 : Ω → 𝓛) (A1 : Ω → 𝒜) (Y : Ω → ℝ)
  (Ypo : 𝒜 → 𝒜 → Ω → ℝ) (L1po : 𝒜 → Ω → 𝓛)

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- The model built from two time point data is nonanticipating: the potential covariate at time
`1` depends only on the treatment at time `0`. -/
theorem ofTwoTime_nonanticipating : (ofTwoTime p L0 A0 L1 A1 Y Ypo L1po).Nonanticipating := by
  intro a a' t h
  fin_cases t
  · rfl
  · simp [ofTwoTime, h 0 (by decide)]

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- Covariate consistency of the model built from two time point data is the two time point
covariate consistency `A0 = a0 ⇒ L1 = L1po a0` used in `gFormula2_dynamic`. -/
theorem ofTwoTime_covariateConsistent_iff :
    (ofTwoTime p L0 A0 L1 A1 Y Ypo L1po).CovariateConsistent ↔
      ∀ ω a0, A0 ω = a0 → L1 ω = L1po a0 ω := by
  constructor
  · intro h ω a0 h0
    exact h ![a0, a0] ω 1 fun s hs => by
      fin_cases s
      · simpa [ofTwoTime] using h0
      · exact absurd hs (by decide)
  · intro h a ω t ht
    fin_cases t
    · rfl
    · exact h ω (a 0) (ht 0 (by decide))

omit [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- Outcome consistency of the model built from two time point data, for every static regime,
is the two time point outcome consistency `A0 = a0, A1 = a1 ⇒ Y = Ypo a0 a1` used in
`gFormula2_dynamic`. -/
theorem ofTwoTime_outcomeConsistent_iff :
    (∀ a, (ofTwoTime p L0 A0 L1 A1 Y Ypo L1po).OutcomeConsistent a) ↔
      ∀ ω a0 a1, A0 ω = a0 → A1 ω = a1 → Y ω = Ypo a0 a1 ω := by
  constructor
  · intro h ω a0 a1 h0 h1
    exact ((ofTwoTime p L0 A0 L1 A1 Y Ypo L1po).outcomeConsistent_iff_two ![a0, a1]).1
      (h ![a0, a1]) ω h0 h1
  · intro h a
    exact ((ofTwoTime p L0 A0 L1 A1 Y Ypo L1po).outcomeConsistent_iff_two a).2
      fun ω h0 h1 => h ω (a 0) (a 1) h0 h1

end OfTwoTime

end Model

/-- **The two time point weighted mean equals the two time point g-formula**, as an identity of
finite sums with no causal hypothesis and no positivity hypothesis: on a block where the final
history event has zero mass both sides contain a zero weighted sum. This is a public restatement
of the identity used in `Weighting.lean` to prove `ipw2_static`. -/
theorem ipw2_eq_gFormula2_static (m : Ω → ℝ) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜)
    (L1 : Ω → 𝓛) (A1 : Ω → 𝒜) (a0 a1 : 𝒜) (Y : Ω → ℝ) :
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

end Longitudinal

end CausalInference
