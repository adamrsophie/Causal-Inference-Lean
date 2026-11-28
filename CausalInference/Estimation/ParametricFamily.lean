/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Estimator
public import CausalInference.PartialIdentification.IdentifiedSet
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Basic

/-!
# Dominated parametric families of densities

A dominated parametric family is a measure `ν` on a sample space `S`, a parameter set `Θ` in a
parameter type `P`, and for each `θ ∈ Θ` a probability density `f(·;θ)` with respect to `ν`. The
law of one observation is `P_θ = f(·;θ) ν`. The parameter type is arbitrary here; the score and
information files take `P = ℝ` (scalar parameter) and `P = Fin p → ℝ` (vector parameter).

## Main definitions

* `CausalInference.ParametricFamily P S`: the family.
* `CausalInference.ParametricFamily.law F θ`: the law `P_θ`.
* `CausalInference.ParametricFamily.pi F n`: the family of an i.i.d. sample of size `n`, with
  sample space `Fin n → S`, dominating measure `ν^n` and joint density `∏_i f(x_i;θ)` (the
  likelihood).

## Main results

* `CausalInference.ParametricFamily.integral_law`, `integrable_law_iff`: change of measure,
  `E_θ[h] = ∫ f(·;θ) h dν`.
* `CausalInference.ParametricFamily.ae_law_pos`: under `P_θ` the density is almost surely
  positive.
* `CausalInference.ParametricFamily.law_eq_law_iff` and `pointIdentified_law_iff`: two parameters
  have the same law if and only if their densities agree `ν`-almost everywhere, so point
  identification of `θ` from the law (`CausalInference.PointIdentified`) is identifiability of
  the densities.
* `CausalInference.ParametricFamily.pi_law`: the law of the sample family is the product law.
* `CausalInference.IsIIDSample.map_fin_eq_pi`: the first `n` observations of an i.i.d. sample
  have the product law, which connects the sample family to `CausalInference.IsIIDSample`.

References: E. L. Lehmann and G. Casella (1998), *Theory of Point Estimation*, 2nd edition,
chapter 1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace CausalInference

/-- A dominated parametric family: a dominating measure `ν` on the sample space `S`, a parameter
set `Θ ⊆ P`, and a density `density θ = f(·;θ)` defined for every `θ : P` (so that derivatives in
the parameter make sense), which is a probability density with respect to `ν` for `θ ∈ Θ`. -/
structure ParametricFamily (P S : Type*) [MeasurableSpace S] where
  /-- The dominating measure `ν`. -/
  ν : Measure S
  /-- The parameter set `Θ`. -/
  Θ : Set P
  /-- The density `density θ x = f(x;θ)`. -/
  density : P → S → ℝ
  /-- Each `f(·;θ)` is measurable. -/
  measurable_density : ∀ θ, Measurable (density θ)
  /-- On `Θ` the densities are nonnegative. -/
  density_nonneg : ∀ θ ∈ Θ, ∀ x, 0 ≤ density θ x
  /-- On `Θ` the densities are `ν`-integrable. -/
  integrable_density : ∀ θ ∈ Θ, Integrable (density θ) ν
  /-- On `Θ` the densities integrate to one. -/
  integral_density : ∀ θ ∈ Θ, ∫ x, density θ x ∂ν = 1

namespace ParametricFamily

variable {P S : Type*} [MeasurableSpace S] (F : ParametricFamily P S)

/-- The law `P_θ = f(·;θ) ν` of one observation. -/
noncomputable def law (θ : P) : Measure S :=
  F.ν.withDensity fun x ↦ ENNReal.ofReal (F.density θ x)

variable {F}

/-- For `θ ∈ Θ`, the law `P_θ` is a probability measure. -/
theorem isProbabilityMeasure_law {θ : P} (hθ : θ ∈ F.Θ) : IsProbabilityMeasure (F.law θ) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (F.integrable_density θ hθ)
      (Eventually.of_forall (F.density_nonneg θ hθ)), F.integral_density θ hθ,
    ENNReal.ofReal_one]

/-- Change of measure: `E_θ[h] = ∫ f(x;θ) h(x) dν(x)` for every `h` (if `h` is not
`P_θ`-integrable, both sides are Bochner integrals of non integrable functions). -/
theorem integral_law {θ : P} (hθ : θ ∈ F.Θ) (h : S → ℝ) :
    ∫ x, h x ∂F.law θ = ∫ x, F.density θ x * h x ∂F.ν := by
  rw [law, integral_withDensity_eq_integral_toReal_smul
    (F.measurable_density θ).ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp [ENNReal.toReal_ofReal (F.density_nonneg θ hθ x)]

/-- Integrability under `P_θ` is integrability of `f(·;θ) h` under `ν`. -/
theorem integrable_law_iff {θ : P} (hθ : θ ∈ F.Θ) {h : S → ℝ} :
    Integrable h (F.law θ) ↔ Integrable (fun x ↦ F.density θ x * h x) F.ν := by
  rw [law, integrable_withDensity_iff_integrable_smul'
    (F.measurable_density θ).ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun x ↦ ?_)
  simp [ENNReal.toReal_ofReal (F.density_nonneg θ hθ x)]

/-- Under `P_θ` the density at the observation is almost surely positive. -/
theorem ae_law_pos {θ : P} : ∀ᵐ x ∂F.law θ, 0 < F.density θ x := by
  rw [law, ae_withDensity_iff (F.measurable_density θ).ennreal_ofReal]
  exact ae_of_all _ fun x hx ↦ by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le] at hx
    exact hx

/-- A `ν`-almost everywhere statement holds `P_θ`-almost surely. -/
theorem ae_law_of_ae {θ : P} {q : S → Prop} (h : ∀ᵐ x ∂F.ν, q x) : ∀ᵐ x ∂F.law θ, q x :=
  (withDensity_absolutelyContinuous _ _).ae_le h

/-- Two parameters of `Θ` have the same law if and only if their densities agree `ν`-almost
everywhere. -/
theorem law_eq_law_iff {θ θ' : P} (hθ : θ ∈ F.Θ) (hθ' : θ' ∈ F.Θ) :
    F.law θ = F.law θ' ↔ F.density θ =ᵐ[F.ν] F.density θ' := by
  rw [law, law, withDensity_eq_iff (F.measurable_density θ).ennreal_ofReal.aemeasurable
    (F.measurable_density θ').ennreal_ofReal.aemeasurable]
  · constructor
    · intro h
      filter_upwards [h] with x hx
      exact (ENNReal.ofReal_eq_ofReal_iff (F.density_nonneg θ hθ x)
        (F.density_nonneg θ' hθ' x)).1 hx
    · intro h
      filter_upwards [h] with x hx
      rw [hx]
  · rw [← ofReal_integral_eq_lintegral_ofReal (F.integrable_density θ hθ)
      (Eventually.of_forall (F.density_nonneg θ hθ))]
    exact ENNReal.ofReal_ne_top

/-- **Identifiability.** The parameter is point identified on `Θ` from the law of an observation
(`CausalInference.PointIdentified`, with the law as observation and the identity as parameter)
if and only if distinct parameters of `Θ` have densities that differ on a set of positive
`ν`-measure. -/
theorem pointIdentified_law_iff :
    PointIdentified F.Θ F.law id ↔
      ∀ θ ∈ F.Θ, ∀ θ' ∈ F.Θ, F.density θ =ᵐ[F.ν] F.density θ' → θ = θ' := by
  refine forall₂_congr fun θ hθ ↦ forall₂_congr fun θ' hθ' ↦ ?_
  rw [law_eq_law_iff hθ hθ']
  rfl

/-! ### The family of an i.i.d. sample of size `n` -/

variable (F) in
/-- The family of an i.i.d. sample of size `n`: sample space `Fin n → S`, dominating measure the
product `ν^n`, the same parameter set, and joint density the likelihood
`L_n(θ; x) = ∏_i f(x_i;θ)`. The dominating measure is assumed σ-finite, as the product measure
requires. -/
noncomputable def pi [SigmaFinite F.ν] (n : ℕ) : ParametricFamily P (Fin n → S) where
  ν := Measure.pi fun _ ↦ F.ν
  Θ := F.Θ
  density θ x := ∏ i, F.density θ (x i)
  measurable_density θ := Finset.measurable_prod _ fun i _ ↦
    (F.measurable_density θ).comp (measurable_pi_apply i)
  density_nonneg θ hθ x := Finset.prod_nonneg fun i _ ↦ F.density_nonneg θ hθ (x i)
  integrable_density θ hθ := Integrable.fintype_prod fun _ ↦ F.integrable_density θ hθ
  integral_density θ hθ := by
    rw [integral_fintype_prod_eq_prod (f := fun _ ↦ F.density θ)]
    simp [F.integral_density θ hθ]

variable [SigmaFinite F.ν]

/-- The law of the sample family is the product of the laws of one observation: under
`(F.pi n).law θ` the coordinates are i.i.d. with law `P_θ`. Both measures agree on boxes, by
Fubini for a product of indicators. -/
theorem pi_law (n : ℕ) {θ : P} (hθ : θ ∈ F.Θ) :
    (F.pi n).law θ = Measure.pi fun _ ↦ F.law θ := by
  have := isProbabilityMeasure_law hθ
  symm
  refine Measure.pi_eq fun s hs ↦ ?_
  have hlaw_i : ∀ i, F.law θ (s i) =
      ENNReal.ofReal (∫ x, (s i).indicator (F.density θ) x ∂F.ν) := fun i ↦ by
    rw [law, withDensity_apply _ (hs i), integral_indicator (hs i),
      ofReal_integral_eq_lintegral_ofReal (F.integrable_density θ hθ).integrableOn
        (ae_of_all _ (F.density_nonneg θ hθ))]
  have hprod : (Set.univ.pi s).indicator (fun x : Fin n → S ↦ ∏ i, F.density θ (x i)) =
      fun x ↦ ∏ i, (s i).indicator (F.density θ) (x i) := by
    ext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ ↦
        (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_univ_pi] using hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  have hint := ((F.pi n).integrable_density θ hθ).integrableOn (s := Set.univ.pi s)
  rw [law, withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ ((F.pi n).density_nonneg θ hθ)),
    ← integral_indicator (MeasurableSet.univ_pi hs)]
  change ENNReal.ofReal (∫ x, (Set.univ.pi s).indicator
    (fun x : Fin n → S ↦ ∏ i, F.density θ (x i)) x ∂Measure.pi fun _ ↦ F.ν) = _
  rw [hprod, integral_fintype_prod_eq_prod (f := fun i ↦ (s i).indicator (F.density θ)),
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ integral_nonneg fun x ↦
      Set.indicator_nonneg (fun y _ ↦ F.density_nonneg θ hθ y) x]
  exact Finset.prod_congr rfl fun i _ ↦ (hlaw_i i).symm

end ParametricFamily

/-- The first `n` observations of an i.i.d. sample have the product law: the law of
`ω ↦ (O 0 ω, …, O (n - 1) ω)` is `(μ.map (O 0))^n`. -/
theorem IsIIDSample.map_fin_eq_pi {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪]
    {O : ℕ → Ω → 𝒪} {μ : Measure Ω} [IsProbabilityMeasure μ] (hO : IsIIDSample O μ) (n : ℕ) :
    μ.map (fun ω (i : Fin n) ↦ O i ω) = Measure.pi fun _ ↦ μ.map (O 0) := by
  have hind : iIndepFun (fun (i : Fin n) ↦ O i) μ := hO.indep.precomp Fin.val_injective
  rw [iIndepFun.map_fun_eq_pi_map (f := fun (i : Fin n) ↦ O i) (fun i ↦ hO.aemeasurable i) hind]
  congr 1
  funext i
  exact (hO.ident i).map_eq

end CausalInference
