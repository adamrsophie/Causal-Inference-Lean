/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MissingData.Weighting
public import CausalInference.PointTreatment.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.ConditionalProbability

/-!
# Transport: source and target populations, the density ratio and structural invariance

A **source** population, where a study was run, and a **target** population, where its results
are to be used, share a covariate space `𝒳`. They are represented by two probability spaces:
the source `(Ω₁, μ₁)` with covariates `X₁` and an outcome `Y₁` (a potential outcome of the
study, in the applications), and the target `(Ω₂, μ₂)` with covariates `X₂` and outcome `Y₂`.

**Why two spaces.** The source and the target are separate populations, often studied by
separate designs; nothing links a source unit to a target unit, and in the applications the
target is known only through the law of its covariates. Two measures say exactly this. The
single measure form with a population indicator `S` (Pearl and Bareinboim 2011; Dahabreh and
coauthors 2019) is recovered by conditioning on `S`: `μ₁ = μ[| S = 1]` and `μ₂ = μ[| S = 0]`
(`isCommonRegression_cond_of_condExp_prodMk`).

**The density ratio.** When the covariate law of the target is absolutely continuous with
respect to that of the source (overlap of the populations), the Radon and Nikodym derivative
`w = dP*_X / dP_X` reweights the source to the target: `∫ g dP*_X = E₁[w(X₁) g(X₁)]`.

**Structural invariance** (conditional mean transportability): one measurable `g` is a version
of `E[Y | X]` in both populations.

## Main definitions

* `densityRatio μ₁ X₁ μ₂ X₂`: the density ratio `dP*_X / dP_X` as a real function.
* `IsCommonRegression μ₁ X₁ Y₁ μ₂ X₂ Y₂ g`: `g(X)` is a version of `E[Y | X]` in both
  populations.
* `StructurallyInvariant μ₁ X₁ Y₁ μ₂ X₂ Y₂`: a common regression exists.

## Main results

* `integral_densityRatio_mul`, `integrable_densityRatio_mul_iff`: reweighting a function of the
  covariates.
* `integrable_densityRatio_mul_iff_condExp_abs`: `w(X₁) Y₁` is integrable in the source exactly
  when `E₁[|Y₁| | X₁ = x]` is integrable under the target covariate law.
* `isCommonRegression_cond_of_condExp_prodMk`: the bridge from the single measure form with a
  population indicator.

## References

* J. Pearl and E. Bareinboim, *Transportability of causal and statistical relations: a formal
  approach*, Proceedings of the AAAI Conference on Artificial Intelligence (2011).
* I. J. Dahabreh, S. E. Robertson, E. J. Tchetgen Tchetgen, E. A. Stuart and M. A. Hernán,
  *Generalizing causal inferences from individuals in randomized trials to all trial-eligible
  individuals*, Biometrics 75 (2019).
-/

@[expose] public section

namespace CausalInference

namespace Transport

open MeasureTheory ProbabilityTheory MissingData

variable {Ω₁ Ω₂ 𝒳 : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  [MeasurableSpace 𝒳] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {X₁ : Ω₁ → 𝒳} {X₂ : Ω₂ → 𝒳}

/-! ### The density ratio -/

/-- The **density ratio** of the target covariate law to the source covariate law,
`w = d(μ₂ ∘ X₂⁻¹) / d(μ₁ ∘ X₁⁻¹)`, as a real valued function. -/
noncomputable def densityRatio (μ₁ : Measure Ω₁) (X₁ : Ω₁ → 𝒳) (μ₂ : Measure Ω₂)
    (X₂ : Ω₂ → 𝒳) : 𝒳 → ℝ :=
  fun x => ((μ₂.map X₂).rnDeriv (μ₁.map X₁) x).toReal

theorem measurable_densityRatio (μ₁ : Measure Ω₁) (X₁ : Ω₁ → 𝒳) (μ₂ : Measure Ω₂)
    (X₂ : Ω₂ → 𝒳) : Measurable (densityRatio μ₁ X₁ μ₂ X₂) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem densityRatio_nonneg (μ₁ : Measure Ω₁) (X₁ : Ω₁ → 𝒳) (μ₂ : Measure Ω₂) (X₂ : Ω₂ → 𝒳)
    (x : 𝒳) : 0 ≤ densityRatio μ₁ X₁ μ₂ X₂ x :=
  ENNReal.toReal_nonneg

variable [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]

/-- **Reweighting a function of the covariates**: under overlap `P*_X ≪ P_X`, for a measurable
`g`, `∫ g dP*_X = E₁[w(X₁) g(X₁)]`. No integrability is needed: both sides are integrals of
the same function against the same measure, written two ways. -/
theorem integral_densityRatio_mul (hX₁ : Measurable X₁) (hov : μ₂.map X₂ ≪ μ₁.map X₁)
    {g : 𝒳 → ℝ} (hg : Measurable g) :
    ∫ x, g x ∂(μ₂.map X₂) = ∫ ω, densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * g (X₁ ω) ∂μ₁ := by
  rw [← integral_toReal_rnDeriv_mul hov]
  exact integral_map (f := fun x => densityRatio μ₁ X₁ μ₂ X₂ x * g x) hX₁.aemeasurable
    ((measurable_densityRatio μ₁ X₁ μ₂ X₂).mul hg).aestronglyMeasurable

/-- Integrability under the target covariate law is integrability of the reweighted function in
the source: `Integrable g P*_X ↔ Integrable (w(X₁) g(X₁)) μ₁`. -/
theorem integrable_densityRatio_mul_iff (hX₁ : Measurable X₁) (hov : μ₂.map X₂ ≪ μ₁.map X₁)
    {g : 𝒳 → ℝ} (hg : Measurable g) :
    Integrable (fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * g (X₁ ω)) μ₁ ↔
      Integrable g (μ₂.map X₂) := by
  rw [← integrable_toReal_rnDeriv_mul_iff hov]
  exact (integrable_map_measure ((measurable_densityRatio μ₁ X₁ μ₂ X₂).mul
    hg).aestronglyMeasurable hX₁.aemeasurable).symm

/-- **Two forms of the integrability condition of transport.** Let `h(X₁)` be a version of
`E₁[|Y| | X₁]` with `h` measurable and `Y` integrable in the source. Then `w(X₁) Y` is
integrable in the source exactly when `h` is integrable under the target covariate law. Both are
the finiteness of `E₁[w(X₁) |Y|] = E₁[w(X₁) h(X₁)]`, an identity of lower integrals obtained by
conditioning on `X₁`. -/
theorem integrable_densityRatio_mul_iff_condExp_abs (hX₁ : Measurable X₁)
    (hov : μ₂.map X₂ ≪ μ₁.map X₁) {Y : Ω₁ → ℝ} (hYm : Measurable Y) (hY : Integrable Y μ₁)
    {h : 𝒳 → ℝ} (hh : Measurable h)
    (Hh : μ₁[fun ω => |Y ω| | MeasurableSpace.comap X₁ inferInstance] =ᵐ[μ₁]
      fun ω => h (X₁ ω)) :
    Integrable (fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * Y ω) μ₁ ↔
      Integrable h (μ₂.map X₂) := by
  rw [← integrable_densityRatio_mul_iff hX₁ hov hh]
  set w := densityRatio μ₁ X₁ μ₂ X₂
  have hwm := measurable_densityRatio μ₁ X₁ μ₂ X₂
  have hm : MeasurableSpace.comap X₁ inferInstance ≤ mΩ₁ := hX₁.comap_le
  have hG : Measurable[MeasurableSpace.comap X₁ inferInstance]
      (fun ω => ENNReal.ofReal (w (X₁ ω))) :=
    (ENNReal.measurable_ofReal.comp hwm).comp (comap_measurable X₁)
  have hh0 : 0 ≤ᵐ[μ₁] fun ω => h (X₁ ω) := by
    filter_upwards [condExp_nonneg (m := MeasurableSpace.comap X₁ inferInstance) (μ := μ₁)
      (Filter.Eventually.of_forall fun ω => abs_nonneg (Y ω) :
        0 ≤ᵐ[μ₁] fun ω => |Y ω|), Hh] with ω h1 h2
    rw [← h2]; exact h1
  have key := lintegral_ofReal_mul_eq_of_condExp_eq hm hY.abs
    (Filter.Eventually.of_forall fun ω => abs_nonneg (Y ω)) Hh hG
  have hmeas1 : AEStronglyMeasurable (fun ω => w (X₁ ω) * Y ω) μ₁ :=
    ((hwm.comp hX₁).mul hYm).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun ω => w (X₁ ω) * h (X₁ ω)) μ₁ :=
    ((hwm.comp hX₁).mul (hh.comp hX₁)).aestronglyMeasurable
  have e1 : ∫⁻ ω, ‖w (X₁ ω) * Y ω‖ₑ ∂μ₁ =
      ∫⁻ ω, ENNReal.ofReal |Y ω| * ENNReal.ofReal (w (X₁ ω)) ∂μ₁ := by
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ofReal_norm, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (densityRatio_nonneg μ₁ X₁ μ₂ X₂ _), mul_comm]
  have e2 : ∫⁻ ω, ‖w (X₁ ω) * h (X₁ ω)‖ₑ ∂μ₁ =
      ∫⁻ ω, ENNReal.ofReal (h (X₁ ω)) * ENNReal.ofReal (w (X₁ ω)) ∂μ₁ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hh0] with ω h0
    rw [← ENNReal.ofReal_mul h0, ← ofReal_norm, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (densityRatio_nonneg μ₁ X₁ μ₂ X₂ _), abs_of_nonneg h0, mul_comm]
  simp only [Integrable, hmeas1, hmeas2, true_and, HasFiniteIntegral, e1, e2, key]

/-! ### Structural invariance -/

/-- `g(X)` is a version of `E[Y | X]` in both populations: `g` is measurable,
`g(X₁) = E₁[Y₁ | X₁]` and `g(X₂) = E₂[Y₂ | X₂]` almost everywhere. -/
def IsCommonRegression (μ₁ : Measure Ω₁) (X₁ : Ω₁ → 𝒳) (Y₁ : Ω₁ → ℝ) (μ₂ : Measure Ω₂)
    (X₂ : Ω₂ → 𝒳) (Y₂ : Ω₂ → ℝ) (g : 𝒳 → ℝ) : Prop :=
  Measurable g ∧
    (fun ω => g (X₁ ω)) =ᵐ[μ₁] μ₁[Y₁ | MeasurableSpace.comap X₁ inferInstance] ∧
    (fun ω => g (X₂ ω)) =ᵐ[μ₂] μ₂[Y₂ | MeasurableSpace.comap X₂ inferInstance]

/-- **Structural invariance** (conditional mean transportability): the conditional mean of the
outcome given the covariates is the same function in the source and in the target. -/
def StructurallyInvariant (μ₁ : Measure Ω₁) (X₁ : Ω₁ → 𝒳) (Y₁ : Ω₁ → ℝ) (μ₂ : Measure Ω₂)
    (X₂ : Ω₂ → 𝒳) (Y₂ : Ω₂ → ℝ) : Prop :=
  ∃ g, IsCommonRegression μ₁ X₁ Y₁ μ₂ X₂ Y₂ g

/-! ### The single measure form with a population indicator -/

section Indicator

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : Ω → 𝒳} {S : Ω → Bool}

omit [MeasurableSpace 𝒳] [IsFiniteMeasure μ] in
/-- A set integral under conditioning on an event: `∫_A f dμ[| E] = μ(E)⁻¹ ∫_{A ∩ E} f dμ`. -/
theorem setIntegral_cond_eq {E A : Set Ω} (hA : MeasurableSet A) (f : Ω → ℝ) :
    ∫ ω in A, f ω ∂(μ[| E]) = (μ E)⁻¹.toReal * ∫ ω in A ∩ E, f ω ∂μ := by
  rw [ProbabilityTheory.cond, Measure.restrict_smul, integral_smul_measure,
    Measure.restrict_restrict hA, smul_eq_mul]

/-- **Conditioning on the population.** In the single measure form, if `g(X)` is a version of
`E[Y | X, S]` (the conditional mean does not depend on the population indicator `S`), then
`g(X)` is a version of `E[Y | X]` under `μ[| S = s]` for each population `s` of positive
probability. The defining set integrals over `{X ∈ B}` under `μ[| S = s]` are set integrals over
`{X ∈ B, S = s}` under `μ`, an event of `σ(X, S)`. -/
theorem condExp_cond_eq_of_condExp_prodMk (hX : Measurable X) (hS : Measurable S) {Y : Ω → ℝ}
    (hY : Integrable Y μ) {g : 𝒳 → ℝ} (hg : Measurable g)
    (H : μ[Y | MeasurableSpace.comap (fun ω => (X ω, S ω)) inferInstance] =ᵐ[μ]
      fun ω => g (X ω)) (s : Bool) (hs0 : μ (S ⁻¹' {s}) ≠ 0) :
    (μ[| S ⁻¹' {s}])[Y | MeasurableSpace.comap X inferInstance] =ᵐ[μ[| S ⁻¹' {s}]]
      fun ω => g (X ω) := by
  have hs : MeasurableSet (S ⁻¹' {s}) := hS (measurableSet_singleton s)
  have hXS : MeasurableSpace.comap (fun ω => (X ω, S ω)) inferInstance ≤ mΩ :=
    (hX.prodMk hS).comap_le
  have := cond_isProbabilityMeasure hs0
  have hgi : Integrable (fun ω => g (X ω)) μ := integrable_condExp.congr H
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le
    (PointTreatment.integrable_cond hY _)
    (fun A _ _ => (PointTreatment.integrable_cond hgi _).integrableOn) ?_
    (hg.comp (comap_measurable X)).aestronglyMeasurable).symm
  rintro _ ⟨B, hB, rfl⟩ _
  rw [setIntegral_cond_eq (hX hB), setIntegral_cond_eq (hX hB)]
  congr 1
  have hE : MeasurableSet[MeasurableSpace.comap (fun ω => (X ω, S ω)) inferInstance]
      (X ⁻¹' B ∩ S ⁻¹' {s}) :=
    ⟨B ×ˢ {s}, hB.prod (measurableSet_singleton s), by ext ω; simp⟩
  rw [← setIntegral_condExp hXS hY hE]
  exact integral_congr_ae (ae_restrict_of_ae H.symm)

/-- **The bridge from the single measure form.** If `g(X)` is a version of `E[Y | X, S]`, and
both populations have positive probability, then `g` is a common regression for the source
`μ[| S = 1]` and the target `μ[| S = 0]`, both on `Ω` with covariates `X` and outcome `Y`. -/
theorem isCommonRegression_cond_of_condExp_prodMk (hX : Measurable X) (hS : Measurable S)
    {Y : Ω → ℝ} (hY : Integrable Y μ) {g : 𝒳 → ℝ} (hg : Measurable g)
    (H : μ[Y | MeasurableSpace.comap (fun ω => (X ω, S ω)) inferInstance] =ᵐ[μ]
      fun ω => g (X ω)) (h1 : μ (S ⁻¹' {true}) ≠ 0) (h0 : μ (S ⁻¹' {false}) ≠ 0) :
    IsCommonRegression (μ[| S ⁻¹' {true}]) X Y (μ[| S ⁻¹' {false}]) X Y g :=
  ⟨hg, (condExp_cond_eq_of_condExp_prodMk hX hS hY hg H true h1).symm,
    (condExp_cond_eq_of_condExp_prodMk hX hS hY hg H false h0).symm⟩

end Indicator

end Transport

end CausalInference
