/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Basic
public import CausalInference.PointTreatment.OutcomeSwap
public import Mathlib.Probability.UniformOn

/-!
# Transport: generalizability to the source population

A study samples units from a source population `(Ω, μ)`; `R ω = true` when unit `ω` is included
in the study. The study is **generalizable** for an outcome `Y` (a potential outcome, in the
applications) when the mean of `Y` among the included units, the complete case mean
`completeCaseMean μ R Y = E[Y | R = 1]`, is the population mean `E[Y]` (Cole and Stuart 2010;
Dahabreh and coauthors 2019).

* Mean independence of `Y` from inclusion, `E[Y | R] = E[Y]`, gives generalizability
  (`completeCaseMean_eq_of_condExp_eq_const`).
* Conditional mean independence given covariates, `E[Y | X, R] = E[Y | X]`, with positive
  inclusion probabilities, licenses **standardization**: `E[Y] = E[m(1, X)]` for any version
  `m(R, X)` of the regression `E[Y | X, R]` (`integral_eq_integral_regression_of_meanIgnorable`).
  This is the outcome swap of the point treatment layer, with inclusion in the role of the
  treatment and the same outcome in both arms.
* Conditional mean independence with overlap does **not** make the unadjusted mean of the
  included units equal to the population mean (`not_generalizable_example`): on four units of
  mass `1/4`, with `X = 1{ω ≥ 2}`, `R = 1{ω ≠ 0}` and `Y = X`, the included mean is `2/3` while
  the population mean is `1/2`.

## Main results

* `completeCaseMean_eq_of_condExp_eq_const`.
* `integral_eq_integral_regression_of_meanIgnorable`.
* `not_generalizable_example`.

## References

* S. R. Cole and E. A. Stuart, *Generalizing evidence from randomized clinical trials to target
  populations: the ACTG 320 trial*, American Journal of Epidemiology 172 (2010).
* I. J. Dahabreh, S. E. Robertson, E. J. Tchetgen Tchetgen, E. A. Stuart and M. A. Hernán,
  *Generalizing causal inferences from individuals in randomized trials to all trial-eligible
  individuals*, Biometrics 75 (2019).
-/

@[expose] public section

namespace CausalInference

namespace Transport

open MeasureTheory ProbabilityTheory MissingData PointTreatment

variable {Ω 𝒳 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒳] {μ : Measure Ω}
  [IsFiniteMeasure μ] {R : Ω → Bool} {X : Ω → 𝒳} {Y : Ω → ℝ}

omit [MeasurableSpace 𝒳] in
/-- **Mean independence of inclusion gives generalizability.** If `E[Y | R] = E[Y]` almost
everywhere, `Y` is integrable and `P(R = 1) > 0`, the mean of `Y` among the included units is
the population mean. -/
theorem completeCaseMean_eq_of_condExp_eq_const (hR : Measurable R) (hY : Integrable Y μ)
    (hind : μ[Y | MeasurableSpace.comap R inferInstance] =ᵐ[μ] fun _ => ∫ ω, Y ω ∂μ)
    (hpos : μ (R ⁻¹' {true}) ≠ 0) :
    completeCaseMean μ R Y = ∫ ω, Y ω ∂μ := by
  have hs : MeasurableSet[MeasurableSpace.comap R inferInstance] (R ⁻¹' {true}) :=
    ⟨{true}, measurableSet_singleton true, rfl⟩
  have hne : μ.real (R ⁻¹' {true}) ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hpos, measure_ne_top _ _⟩
  rw [completeCaseMean, ← Measure.restrict_univ (μ := μ[|R ⁻¹' {true}]),
    setIntegral_cond_eq MeasurableSet.univ, Set.univ_inter,
    ← setIntegral_condExp hR.comap_le hY hs,
    setIntegral_congr_ae (hR.comap_le _ hs) (hind.mono fun _ h _ => h), setIntegral_const,
    smul_eq_mul, ENNReal.toReal_inv, ← measureReal_def, ← mul_assoc, inv_mul_cancel₀ hne,
    one_mul]

/-- **Standardization to the source population.** Let `π(X)` be a version of the inclusion
probability `P(R = 1 | X)`, positive almost surely (overlap), and `m(R, X)` a version of the
regression `E[Y | X, R]` of an integrable outcome. If `E[Y | X, R] = E[Y | X]` (conditional mean
independence of inclusion), then `m(1, X)` is a version of `E[Y | X]` and
`E[Y] = E[m(1, X)] = ∫ m(1, x) dP_X(x)`. -/
theorem integral_eq_integral_regression_of_meanIgnorable (hR : Measurable R)
    (hX : Measurable X) (hY : Integrable Y μ) {π : 𝒳 → ℝ}
    (hps : IsPropensityScore μ R X π) (hpos : ∀ᵐ ω ∂μ, 0 < π (X ω)) {m : Bool → 𝒳 → ℝ}
    (hreg : IsOutcomeRegression μ R X Y m)
    (hind : μ[Y | MeasurableSpace.comap (fun ω => (X ω, R ω)) inferInstance] =ᵐ[μ]
      μ[Y | MeasurableSpace.comap X inferInstance]) :
    (fun ω => m true (X ω)) =ᵐ[μ] μ[Y | MeasurableSpace.comap X inferInstance] ∧
      ∫ ω, Y ω ∂μ = ∫ ω, m true (X ω) ∂μ ∧ ∫ ω, Y ω ∂μ = ∫ x, m true x ∂(μ.map X) := by
  have hobs : obsOutcome R (fun _ => Y) = Y := rfl
  have h := IsOutcomeRegression.ae_eq_condExp_of_pos (Y := fun _ => Y) hX hR
    (hobs ▸ hY) true hY (hobs ▸ hreg) hps hind
  have hae : (fun ω => m true (X ω)) =ᵐ[μ] μ[Y | MeasurableSpace.comap X inferInstance] := by
    filter_upwards [h, hpos] with ω h1 h2
    exact h1 h2
  have e : ∫ ω, Y ω ∂μ = ∫ ω, m true (X ω) ∂μ := by
    rw [integral_congr_ae hae, integral_condExp hX.comap_le]
  exact ⟨hae, e, e.trans (integral_map hX.aemeasurable
    (hreg.1 true).aestronglyMeasurable).symm⟩

/-! ### Conditional mean independence does not give generalizability -/

section Example

/-- The uniform law on four units. -/
noncomputable def selLaw : Measure (Fin 4) := uniformOn Set.univ

instance : IsProbabilityMeasure selLaw := by
  unfold selLaw
  infer_instance

theorem selLaw_real_singleton (ω : Fin 4) : selLaw.real {ω} = 1 / 4 := by
  simp [selLaw, measureReal_def, uniformOn_univ]

/-- The covariate `X = 1{ω ≥ 2}`. -/
def selCov (ω : Fin 4) : Bool := decide (2 ≤ ω.val)

/-- Inclusion `R = 1{ω ≠ 0}`. -/
def selInc (ω : Fin 4) : Bool := decide (ω ≠ 0)

/-- The outcome `Y = X`, as a real number. -/
noncomputable def selOut (ω : Fin 4) : ℝ := if selCov ω then 1 else 0

/-- **Conditional mean independence with overlap does not give generalizability.** In the
four unit model, `E[Y | X, R] = E[Y | X]` (both are `Y`, a function of `X`), every covariate
stratum has included units, at least one unit is included, and yet the mean among the included
units, `2/3`, differs from the population mean `1/2`. -/
theorem not_generalizable_example :
    selLaw[selOut | MeasurableSpace.comap (fun ω => (selCov ω, selInc ω)) inferInstance] =ᵐ[selLaw]
      selLaw[selOut | MeasurableSpace.comap selCov inferInstance] ∧
    (∀ x, selLaw {ω | selInc ω = true ∧ selCov ω = x} ≠ 0) ∧ selLaw (selInc ⁻¹' {true}) ≠ 0 ∧
    completeCaseMean selLaw selInc selOut = 2 / 3 ∧ ∫ ω, selOut ω ∂selLaw = 1 / 2 := by
  have hYX : StronglyMeasurable[MeasurableSpace.comap selCov inferInstance] selOut :=
    ((Measurable.of_discrete (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (comap_measurable selCov)).stronglyMeasurable
  have hle : MeasurableSpace.comap selCov inferInstance ≤
      MeasurableSpace.comap (fun ω => (selCov ω, selInc ω)) inferInstance :=
    (measurable_fst.comp (comap_measurable fun ω => (selCov ω, selInc ω))).comap_le
  have hint : Integrable selOut selLaw := Integrable.of_finite
  have hsR : selInc ⁻¹' {true} = ({1, 2, 3} : Set (Fin 4)) := by
    ext ω; fin_cases ω <;> simp [selInc]
  have hpos : ∀ ω : Fin 4, selLaw {ω} ≠ 0 := fun ω => by
    simp [selLaw, uniformOn_univ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [condExp_of_stronglyMeasurable
      (Measurable.of_discrete (f := fun ω : Fin 4 => (selCov ω, selInc ω))).comap_le
      (hYX.mono hle) hint, condExp_of_stronglyMeasurable
      (Measurable.of_discrete (f := selCov)).comap_le hYX hint]
  · intro x
    cases x
    · refine fun h0 => hpos 1 (measure_mono_null (fun ω h => ?_) h0)
      rw [Set.mem_singleton_iff] at h; subst h; simp [selInc, selCov]
    · refine fun h0 => hpos 2 (measure_mono_null (fun ω h => ?_) h0)
      rw [Set.mem_singleton_iff] at h; subst h; simp [selInc, selCov]
  · refine fun h0 => hpos 1 (measure_mono_null (fun ω h => ?_) h0)
    rw [Set.mem_singleton_iff] at h; subst h; simp [selInc]
  · rw [completeCaseMean, ← Measure.restrict_univ (μ := selLaw[|selInc ⁻¹' {true}]),
      setIntegral_cond_eq MeasurableSet.univ, Set.univ_inter, hsR,
      ← integral_indicator (Set.toFinite _).measurableSet, integral_fintype Integrable.of_finite,
      ENNReal.toReal_inv, ← measureReal_def]
    have h3 : selLaw.real ({1, 2, 3} : Set (Fin 4)) = 3 / 4 := by
      have : ({1, 2, 3} : Set (Fin 4)) = ((({1, 2, 3} : Finset (Fin 4))) : Set (Fin 4)) := by
        simp
      rw [this, measureReal_def, selLaw, uniformOn_univ,
        Measure.count_apply_finset]
      simp
    rw [h3]
    simp [Fin.sum_univ_four, selLaw_real_singleton, selOut, selCov, Set.indicator]
    norm_num
  · rw [integral_fintype Integrable.of_finite]
    simp [Fin.sum_univ_four, selLaw_real_singleton, selOut, selCov]
    norm_num

end Example

end Transport

end CausalInference
