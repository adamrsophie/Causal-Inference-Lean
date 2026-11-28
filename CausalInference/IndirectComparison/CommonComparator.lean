/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.Constancy
public import CausalInference.Measures.LinkScale
public import Mathlib.Probability.Moments.Variance

/-!
# The indirect comparison through a common comparator

Two trials estimate the effects `d_ac` and `d_bc` of the common comparator `c` relative to `a`
and to `b`; the **indirect estimate** of the effect of `b` relative to `a` is
`d̂_ac - d̂_bc` (`indirectEstimate`, Bucher et al. 1997).

* **Identity.** Under constancy of the two direct relative effects across the populations, two
  exact trial contrasts give the effect of `b` relative to `a` in every population, the target
  included (`indirectEstimate_eq_of_constant`).
* **Unbiasedness.** Under the same constancy, integrable estimators unbiased for the trial
  contrasts give an estimator unbiased for the target contrast
  (`integral_indirectEstimate_of_constant`).
* **Variance.** For square integrable uncorrelated estimators the variance of the indirect
  estimate is the sum of the two variances (`variance_indirectEstimate`), in particular for
  independent estimators (`variance_indirectEstimate_of_indepFun`).
* **The price of indirectness.** With positive variances the standard error of the indirect
  estimate is strictly larger than each direct standard error (`sqrt_variance_indirectEstimate`).

All four are instantiated in one concrete model (`indirectEstimate_example`): two populations
with arm means `j + t` on the identity scale, and independent estimators `2 ± 1`, `1 ± 1`.

## Main definitions

* `indirectEstimate`, `signVal`, `uniformPairLaw`.

## Main results

* `indirectEstimate_eq_of_constant`, `integral_indirectEstimate_of_constant`,
  `variance_indirectEstimate`, `variance_indirectEstimate_of_indepFun`,
  `sqrt_variance_indirectEstimate`, `indirectEstimate_example`.

## References

* H. C. Bucher, G. H. Guyatt, L. E. Griffith and S. D. Walter, *The results of direct and
  indirect treatment comparisons in meta-analysis of randomized controlled trials*, Journal of
  Clinical Epidemiology 50 (1997).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory EffectMeasure

/-- The **indirect estimate** `d̂_ac - d̂_bc` of the effect of `b` relative to `a` from estimates
of the effects of the common comparator `c` relative to `a` and to `b`. -/
def indirectEstimate {Ω : Type*} (dac dbc : Ω → ℝ) : Ω → ℝ := fun ω => dac ω - dbc ω

section Identity

variable {J ι 𝒳 : Type*} {Ω : J → Type*} [∀ j, MeasurableSpace (Ω j)] {g : ℝ → ℝ}
  {P : ∀ j, Population (Ω j) 𝒳 ι} {a b c : ι}

/-- **The identity of the indirect comparison.** If the effects of `c` relative to `a` and to `b`
are constant across the populations, then the exact contrasts of the trial populations `P k` and
`P l` give the effect of `b` relative to `a` in every population `P j`. -/
theorem indirectEstimate_eq_of_constant (h : ConstantRelativeEffects g P {(a, c), (b, c)})
    (j k l : J) {Ω' : Type*} (ω : Ω') :
    indirectEstimate (fun _ => (P k).marginalEffect g a c) (fun _ => (P l).marginalEffect g b c)
      ω = (P j).marginalEffect g a b :=
  (marginalEffect_eq_sub_of_constant h j k l).symm

/-- **Unbiasedness of the indirect estimate.** If the effects of `c` relative to `a` and to `b`
are constant across the populations, and integrable estimators `d̂_ac`, `d̂_bc` are unbiased for
the contrasts of the trial populations `P k` and `P l`, then `d̂_ac - d̂_bc` is unbiased for the
effect of `b` relative to `a` in every population `P j`. -/
theorem integral_indirectEstimate_of_constant (h : ConstantRelativeEffects g P {(a, c), (b, c)})
    (j k l : J) {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} {dac dbc : Ω' → ℝ}
    (hac : Integrable dac μ) (hbc : Integrable dbc μ)
    (Eac : ∫ ω, dac ω ∂μ = (P k).marginalEffect g a c)
    (Ebc : ∫ ω, dbc ω ∂μ = (P l).marginalEffect g b c) :
    ∫ ω, indirectEstimate dac dbc ω ∂μ = (P j).marginalEffect g a b := by
  simp only [indirectEstimate]
  rw [integral_sub hac hbc, Eac, Ebc, marginalEffect_eq_sub_of_constant h j k l]

end Identity

section Variance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {dac dbc : Ω → ℝ}

/-- **The variance of the indirect estimate** is the sum of the two variances, for square
integrable uncorrelated estimators. -/
theorem variance_indirectEstimate [IsFiniteMeasure μ] (hac : MemLp dac 2 μ) (hbc : MemLp dbc 2 μ)
    (hcov : cov[dac, dbc; μ] = 0) :
    Var[indirectEstimate dac dbc; μ] = Var[dac; μ] + Var[dbc; μ] := by
  rw [show indirectEstimate dac dbc = fun ω => dac ω - dbc ω from rfl, variance_fun_sub hac hbc,
    hcov, mul_zero, sub_zero]

/-- **The variance of the indirect estimate from independent trials** is the sum of the two
variances, for square integrable independent estimators under a probability measure. -/
theorem variance_indirectEstimate_of_indepFun [IsProbabilityMeasure μ] (hac : MemLp dac 2 μ)
    (hbc : MemLp dbc 2 μ) (hind : IndepFun dac dbc μ) :
    Var[indirectEstimate dac dbc; μ] = Var[dac; μ] + Var[dbc; μ] :=
  variance_indirectEstimate hac hbc (hind.covariance_eq_zero hac hbc)

/-- **The price of indirectness.** For square integrable uncorrelated estimators with positive
variances, the standard error of the indirect estimate is `√(v_ac + v_bc)`, strictly larger than
each direct standard error. -/
theorem sqrt_variance_indirectEstimate [IsFiniteMeasure μ] (hac : MemLp dac 2 μ)
    (hbc : MemLp dbc 2 μ) (hcov : cov[dac, dbc; μ] = 0) (hvac : 0 < Var[dac; μ])
    (hvbc : 0 < Var[dbc; μ]) :
    √(Var[indirectEstimate dac dbc; μ]) = √(Var[dac; μ] + Var[dbc; μ]) ∧
      max √(Var[dac; μ]) √(Var[dbc; μ]) < √(Var[indirectEstimate dac dbc; μ]) := by
  rw [variance_indirectEstimate hac hbc hcov]
  exact ⟨rfl, max_lt (Real.sqrt_lt_sqrt hvac.le (by linarith))
    (Real.sqrt_lt_sqrt hvbc.le (by linarith))⟩

end Variance

/-! ### A concrete instance -/

/-- The sign `±1` of a fair coin. -/
def signVal (v : Bool) : ℝ := if v then 1 else -1

/-- Two independent fair coins. -/
noncomputable def uniformPairLaw : Measure (Bool × Bool) := halfLaw.prod halfLaw

instance : IsProbabilityMeasure uniformPairLaw := by
  unfold uniformPairLaw; infer_instance

/-- The mean under two independent fair coins is the average over the four outcomes. -/
theorem integral_uniformPairLaw (f : Bool × Bool → ℝ) :
    ∫ z, f z ∂uniformPairLaw =
      (f (true, true) + f (true, false) + f (false, true) + f (false, false)) / 4 := by
  rw [uniformPairLaw, integral_prod f (Integrable.of_finite), integral_halfLaw, integral_halfLaw,
    integral_halfLaw]
  ring

theorem memLp_uniformPairLaw (f : Bool × Bool → ℝ) : MemLp f 2 uniformPairLaw :=
  MemLp.of_discrete

/-- **The indirect comparison in a concrete model.** Two populations `P 0`, `P 1` on a point have
arm means `j + t` for the treatments `t = 0, 1, 2`; on the identity scale every relative effect is
constant, with `d_02 = 2`, `d_12 = 1` and `d_01 = 1`. Under two independent fair coins the
estimators `d̂_02 = 2 ± 1` and `d̂_12 = 1 ± 1` are square integrable, independent and unbiased,
with variance `1` each. The indirect estimate is unbiased for `d_01 = 1`, its variance is `2`, and
its standard error `√2` exceeds the direct standard errors `1`. -/
theorem indirectEstimate_example :
    let P : Fin 2 → Population Unit Unit (Fin 3) := fun j => pointPopulation fun t => j + t
    let dac : Bool × Bool → ℝ := fun z => 2 + signVal z.1
    let dbc : Bool × Bool → ℝ := fun z => 1 + signVal z.2
    ConstantRelativeEffects id P {(0, 2), (1, 2)} ∧ IndepFun dac dbc uniformPairLaw ∧
      ∫ z, dac z ∂uniformPairLaw = (P 0).marginalEffect id 0 2 ∧
      ∫ z, dbc z ∂uniformPairLaw = (P 1).marginalEffect id 1 2 ∧
      ∫ z, indirectEstimate dac dbc z ∂uniformPairLaw = (P 0).marginalEffect id 0 1 ∧
      (P 0).marginalEffect id 0 1 = 1 ∧ Var[dac; uniformPairLaw] = 1 ∧
      Var[dbc; uniformPairLaw] = 1 ∧ Var[indirectEstimate dac dbc; uniformPairLaw] = 2 ∧
      max √(Var[dac; uniformPairLaw]) √(Var[dbc; uniformPairLaw]) <
        √(Var[indirectEstimate dac dbc; uniformPairLaw]) := by
  intro P dac dbc
  have hme : ∀ j : Fin 2, ∀ s t : Fin 3,
      (P j).marginalEffect id s t = (t : ℝ) - s := fun j s t => by
    simp only [P, Population.marginalEffect, pointPopulation_armMean, id]; ring
  have hcon : ConstantRelativeEffects id P {(0, 2), (1, 2)} :=
    fun p _ j j' => by rw [hme, hme]
  have hind : IndepFun dac dbc uniformPairLaw :=
    indepFun_prod (X := fun v => 2 + signVal v) (Y := fun v => 1 + signVal v)
      (measurable_of_finite _) (measurable_of_finite _)
  have Eac : ∫ z, dac z ∂uniformPairLaw = 2 := by
    rw [integral_uniformPairLaw]; norm_num [dac, signVal]
  have Ebc : ∫ z, dbc z ∂uniformPairLaw = 1 := by
    rw [integral_uniformPairLaw]; norm_num [dbc, signVal]
  have Vac : Var[dac; uniformPairLaw] = 1 := by
    rw [variance_eq_integral (measurable_of_finite _).aemeasurable, Eac, integral_uniformPairLaw]
    norm_num [dac, signVal]
  have Vbc : Var[dbc; uniformPairLaw] = 1 := by
    rw [variance_eq_integral (measurable_of_finite _).aemeasurable, Ebc, integral_uniformPairLaw]
    norm_num [dbc, signVal]
  have hm2 : ∀ s t : Fin 3, (P 0).marginalEffect id s t = (P 1).marginalEffect id s t :=
    fun s t => by rw [hme, hme]
  have Eac' : ∫ z, dac z ∂uniformPairLaw = (P 0).marginalEffect id 0 2 := by
    rw [Eac, hme]; norm_num
  have Ebc' : ∫ z, dbc z ∂uniformPairLaw = (P 1).marginalEffect id 1 2 := by
    rw [Ebc, hme]; norm_num
  have hV := variance_indirectEstimate_of_indepFun (memLp_uniformPairLaw _)
    (memLp_uniformPairLaw _) hind
  refine ⟨hcon, hind, Eac', Ebc',
    integral_indirectEstimate_of_constant hcon 0 0 1 (Integrable.of_finite)
      (Integrable.of_finite) Eac' Ebc', by rw [hme]; norm_num, Vac, Vbc,
    by rw [hV, Vac, Vbc]; norm_num, ?_⟩
  exact (sqrt_variance_indirectEstimate (memLp_uniformPairLaw _) (memLp_uniformPairLaw _)
    (hind.covariance_eq_zero (memLp_uniformPairLaw _) (memLp_uniformPairLaw _))
    (by rw [Vac]; norm_num) (by rw [Vbc]; norm_num)).2

end IndirectComparison

end CausalInference
