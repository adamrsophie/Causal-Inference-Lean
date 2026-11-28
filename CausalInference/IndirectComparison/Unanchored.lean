/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.Constancy

/-!
# Anchored and unanchored comparisons under an additive arm model

The **additive arm model** for a family of populations `P j` on the scale `g` writes each link
position as a population baseline plus a treatment shift,

`g(E_j[Y(t)]) = μ_j + α_t`, with `α_r = 0` for a reference treatment `r`

(`AdditiveArmModel`). It is a model form of constancy: every relative effect is `α_b - α_a` in
every population (`AdditiveArmModel.marginalEffect_eq`, `AdditiveArmModel.constant`).

* **Anchoring cancels the baselines and the comparator**: the indirect comparison
  `d_ac(P_k) - d_bc(P_l)` is `(α_c - α_a) - (α_c - α_b) = α_b - α_a`, the effect `d_ab` of every
  population (`AdditiveArmModel.indirect_eq`).
* **The unanchored comparison carries the baseline difference**: the difference of link
  positions `g(E_k[Y(b)]) - g(E_l[Y(a)])` of arms read in different populations is
  `(μ_k - μ_l) + d_ab`; its bias for `d_ab` is `μ_k - μ_l`, zero exactly when the baselines agree
  (`AdditiveArmModel.unanchored_sub`). With unbiased estimators of the two positions the expected
  unanchored estimate has the same bias (`AdditiveArmModel.integral_unanchored_sub`).

A concrete model with baselines `0` and `1` (`unanchored_bias_example`) gives the anchored
comparison exactly and the unanchored comparison with bias `-1`.

## Main definitions

* `AdditiveArmModel`.

## Main results

* `AdditiveArmModel.marginalEffect_eq`, `AdditiveArmModel.constant`,
  `AdditiveArmModel.indirect_eq`, `AdditiveArmModel.unanchored_sub`,
  `AdditiveArmModel.integral_unanchored_sub`, `unanchored_bias_example`,
  `unanchored_sampling_example`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory

variable {J ι 𝒳 : Type*} {Ω : J → Type*} [∀ j, MeasurableSpace (Ω j)]

/-- The **additive arm model** on the scale `g`: the link position of treatment `t` in population
`j` is a baseline `base j` plus a treatment shift `α t`, with `α r = 0` for the reference
treatment `r`. -/
def AdditiveArmModel (g : ℝ → ℝ) (P : ∀ j, Population (Ω j) 𝒳 ι) (base : J → ℝ) (α : ι → ℝ)
    (r : ι) : Prop :=
  (∀ j t, g ((P j).armMean t) = base j + α t) ∧ α r = 0

namespace AdditiveArmModel

variable {g : ℝ → ℝ} {P : ∀ j, Population (Ω j) 𝒳 ι} {base : J → ℝ} {α : ι → ℝ} {r : ι}

/-- Under the additive arm model every relative effect is `α_b - α_a`, free of the population. -/
theorem marginalEffect_eq (h : AdditiveArmModel g P base α r) (j : J) (a b : ι) :
    (P j).marginalEffect g a b = α b - α a := by
  rw [Population.marginalEffect, h.1, h.1]; ring

/-- The additive arm model gives constant relative effects for all pairs. -/
theorem constant (h : AdditiveArmModel g P base α r) : ConstantRelativeEffects g P Set.univ :=
  fun p _ j j' => by rw [h.marginalEffect_eq, h.marginalEffect_eq]

/-- The effect of a treatment relative to the reference is its shift. -/
theorem marginalEffect_ref (h : AdditiveArmModel g P base α r) (j : J) (t : ι) :
    (P j).marginalEffect g r t = α t := by
  rw [h.marginalEffect_eq, h.2, sub_zero]

/-- **Anchoring cancels the baselines and the comparator**: the indirect comparison
`d_ac(P_k) - d_bc(P_l)` is `α_b - α_a`, the effect of `b` relative to `a` in every
population. -/
theorem indirect_eq (h : AdditiveArmModel g P base α r) (k l j : J) (a b c : ι) :
    (P k).marginalEffect g a c - (P l).marginalEffect g b c = α b - α a ∧
      (P k).marginalEffect g a c - (P l).marginalEffect g b c = (P j).marginalEffect g a b := by
  rw [h.marginalEffect_eq, h.marginalEffect_eq, h.marginalEffect_eq]
  exact ⟨by ring, by ring⟩

/-- **The unanchored comparison carries the baseline difference.** The difference of the link
positions of `b` in `P_k` and of `a` in `P_l` is `(μ_k - μ_l) + d_ab`, for the effect `d_ab` of
any population; as a comparison of `b` with `a` its bias is `μ_k - μ_l`, which vanishes exactly
when the two baselines agree. -/
theorem unanchored_sub (h : AdditiveArmModel g P base α r) (k l j : J) (a b : ι) :
    g ((P k).armMean b) - g ((P l).armMean a) = (base k - base l) + (P j).marginalEffect g a b ∧
      (g ((P k).armMean b) - g ((P l).armMean a) - (P j).marginalEffect g a b = 0 ↔
        base k = base l) := by
  have e : g ((P k).armMean b) - g ((P l).armMean a) - (P j).marginalEffect g a b =
      base k - base l := by
    rw [h.1, h.1, h.marginalEffect_eq]; ring
  exact ⟨by linarith, by rw [e, sub_eq_zero]⟩

/-- **The sampling bias of the unanchored estimate.** If `η̂_b` and `η̂_a` are integrable and
unbiased for the link positions of `b` in `P_k` and of `a` in `P_l`, the expected unanchored
estimate `E[η̂_b - η̂_a]` exceeds the effect `d_ab` by the baseline difference `μ_k - μ_l`. -/
theorem integral_unanchored_sub (h : AdditiveArmModel g P base α r) (k l j : J) (a b : ι)
    {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} {ηb ηa : Ω' → ℝ} (hb : Integrable ηb μ)
    (ha : Integrable ηa μ) (Eb : ∫ ω, ηb ω ∂μ = g ((P k).armMean b))
    (Ea : ∫ ω, ηa ω ∂μ = g ((P l).armMean a)) :
    ∫ ω, (ηb ω - ηa ω) ∂μ - (P j).marginalEffect g a b = base k - base l := by
  rw [integral_sub hb ha, Eb, Ea, (h.unanchored_sub k l j a b).1]; ring

end AdditiveArmModel

/-- **Anchored against unanchored in a concrete model.** Two populations on a point have arm
means `j + t` for the treatments `t = 0, 1, 2` (baselines `0`, `1`; shifts `0, 1, 2`; reference
`0`) on the identity scale. The anchored comparison `d_02(P_0) - d_12(P_1)` is `1`, the effect
`d_01` of both populations, while the unanchored comparison of arm `1` in `P_0` with arm `0` in
`P_1` is `0`, with bias `-1`. -/
theorem unanchored_bias_example :
    let P : Fin 2 → Population Unit Unit (Fin 3) := fun j => pointPopulation fun t => j + t
    AdditiveArmModel id P (fun j => j) (fun t => t) 0 ∧
      (P 0).marginalEffect id 0 2 - (P 1).marginalEffect id 1 2 = 1 ∧
      (P 0).marginalEffect id 0 1 = 1 ∧ (P 1).marginalEffect id 0 1 = 1 ∧
      id ((P 0).armMean 1) - id ((P 1).armMean 0) = 0 ∧
      id ((P 0).armMean 1) - id ((P 1).armMean 0) - (P 0).marginalEffect id 0 1 = -1 := by
  intro P
  have hA : AdditiveArmModel id P (fun j => j) (fun t => t) 0 :=
    ⟨fun j t => by simp [P, pointPopulation_armMean], by simp⟩
  have hme := hA.marginalEffect_eq
  refine ⟨hA, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hme, hme]; norm_num
  · rw [hme]; norm_num
  · rw [hme]; norm_num
  · simp [P, pointPopulation_armMean]
  · rw [hme]; simp [P, pointPopulation_armMean]

/-- **The sampling bias in the concrete model.** In the model of `unanchored_bias_example`, exact
estimators of the two link positions (constant under a point mass) have an expected unanchored
estimate exceeding `d_01` by the baseline difference `0 - 1 = -1`. -/
theorem unanchored_sampling_example :
    let P : Fin 2 → Population Unit Unit (Fin 3) := fun j => pointPopulation fun t => j + t
    ∫ ω, ((fun _ : Unit => id ((P 0).armMean 1)) ω - (fun _ : Unit => id ((P 1).armMean 0)) ω)
        ∂Measure.dirac () - (P 0).marginalEffect id 0 1 = -1 := by
  intro P
  have hA : AdditiveArmModel id P (fun j => j) (fun t => t) 0 := (unanchored_bias_example).1
  rw [hA.integral_unanchored_sub 0 1 0 0 1 (integrable_const _) (integrable_const _)
    (by simp) (by simp)]
  norm_num

end IndirectComparison

end CausalInference
