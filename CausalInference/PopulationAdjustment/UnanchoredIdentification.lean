/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.AnchoredIdentification

/-!
# The unanchored identification theorem

The unanchored setting (`IndirectComparison.UnanchoredSetting`) has a source of outcomes on `a`,
a separate source of outcomes on `b`, no common comparator, and a target population, all with
covariates in `𝒳`. With conditional mean functions `m_a` of `Y(a)` in the first source and `m_b`
of `Y(b)` in the second, the unanchored estimand on the scale `g` is the marginal estimand
`linkMarginal g Q_X m_a m_b = g(∫ m_b dQ_X) - g(∫ m_a dQ_X)` of the two surfaces under the
target covariate law `Q_X`.

The assumptions (`UnanchoredSetting.IdentificationAssumptions`): measurable covariates;
integrable potential outcomes of the arm used in each source and of both arms in the target;
target arm means in the domain `D` of the link; conditional mean functions in the sources;
**absolute constancy** of each arm from its source to the target (a common conditional mean,
`StructurallyInvariant`); overlap `Q_X ≪ P_X` with each source; and integrable density ratio
weighted outcomes in the sources.

* **Recovery** (`UnanchoredSetting.IdentificationAssumptions.identification`): each source
  surface is a conditional mean function of its arm in the target and is integrable under `Q_X`;
  its standardized value is the target arm mean, which is also the density ratio weighted source
  mean; both standardized values lie in `D`; and the target marginal effect is the unanchored
  estimand.
* **An omitted prognostic variable** (`Population.armMean_omitted_residual`). If the adjustment
  set is `X` while absolute constancy holds only given `(X, W)`, with the joint law of `(X, W)` in
  the source the law of `X` composed with a Markov kernel `κ_src` and in the target composed with
  `κ_*`, the source surface given `X` is the `κ_src` average of the common surface `m(x, w)`, and
  its standardized value misses the target arm mean by the residual
  `∫ (∫ m(x, ·) dκ_src x - ∫ m(x, ·) dκ_* x) dQ_X`. The bias vanishes when `κ_src = κ_*`, that
  is, when `W` is balanced given `X`, and also whenever the two averages of `m(x, ·)` agree for
  `Q_X` almost every `x`, even with imbalance.

Where the parts come from: recovery is
`PopulationAdjustment.integral_covLaw_eq_armMean_of_structurallyInvariant`,
`PopulationAdjustment.armMean_eq_integral_densityRatio_mul` and
`IndirectComparison.UnanchoredSetting.marginalEffect_target_eq`; the residual is
`Population.IsCondMean.kernelAverage` and
`PopulationAdjustment.integral_kernelAverage_sub_integral_compProd`.

## Main definitions

* `UnanchoredSetting.IdentificationAssumptions`.

## Main results

* `UnanchoredSetting.IdentificationAssumptions.identification`.
* `Population.armMean_omitted_residual`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory EffectMeasure Transport PopulationAdjustment

/-! ### Recovery under absolute constancy -/

namespace UnanchoredSetting

variable {Ω₁ Ω₂ Ω₃ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
  [MeasurableSpace 𝒳]

/-- **The assumptions of the unanchored identification theorem** for the surfaces `m_a` (first
source) and `m_b` (second source) and the domain `D` of the link; they do not depend on the
scale. -/
structure IdentificationAssumptions (S : UnanchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι) (D : Set ℝ)
    (ma mb : 𝒳 → ℝ) : Prop where
  /-- The covariate of the first source is measurable. -/
  measurable_sourceA : Measurable S.sourceA.X
  /-- The covariate of the second source is measurable. -/
  measurable_sourceB : Measurable S.sourceB.X
  /-- The target covariate is measurable. -/
  measurable_target : Measurable S.target.X
  /-- The potential outcome of `a` is integrable in the first source. -/
  integrable_sourceA : Integrable (S.sourceA.Y S.a) S.sourceA.μ
  /-- The potential outcome of `b` is integrable in the second source. -/
  integrable_sourceB : Integrable (S.sourceB.Y S.b) S.sourceB.μ
  /-- The potential outcome of `a` is integrable in the target. -/
  integrable_target_a : Integrable (S.target.Y S.a) S.target.μ
  /-- The potential outcome of `b` is integrable in the target. -/
  integrable_target_b : Integrable (S.target.Y S.b) S.target.μ
  /-- The target mean of `Y(a)` lies in the domain of the link. -/
  mem_a : S.target.armMean S.a ∈ D
  /-- The target mean of `Y(b)` lies in the domain of the link. -/
  mem_b : S.target.armMean S.b ∈ D
  /-- `m_a` is a conditional mean function of `Y(a)` in the first source. -/
  isCondMean_a : S.sourceA.IsCondMean S.a ma
  /-- `m_b` is a conditional mean function of `Y(b)` in the second source. -/
  isCondMean_b : S.sourceB.IsCondMean S.b mb
  /-- Absolute constancy of arm `a` from the first source to the target. -/
  structurallyInvariant_a : StructurallyInvariant S.sourceA.μ S.sourceA.X (S.sourceA.Y S.a)
    S.target.μ S.target.X (S.target.Y S.a)
  /-- Absolute constancy of arm `b` from the second source to the target. -/
  structurallyInvariant_b : StructurallyInvariant S.sourceB.μ S.sourceB.X (S.sourceB.Y S.b)
    S.target.μ S.target.X (S.target.Y S.b)
  /-- Overlap of the target with the first source. -/
  overlap_a : S.target.covLaw ≪ S.sourceA.covLaw
  /-- Overlap of the target with the second source. -/
  overlap_b : S.target.covLaw ≪ S.sourceB.covLaw
  /-- The density ratio weighted outcome of `a` is integrable in the first source. -/
  integrable_weighted_a : Integrable (fun ω => densityRatio S.sourceA.μ S.sourceA.X S.target.μ
    S.target.X (S.sourceA.X ω) * S.sourceA.Y S.a ω) S.sourceA.μ
  /-- The density ratio weighted outcome of `b` is integrable in the second source. -/
  integrable_weighted_b : Integrable (fun ω => densityRatio S.sourceB.μ S.sourceB.X S.target.μ
    S.target.X (S.sourceB.X ω) * S.sourceB.Y S.b ω) S.sourceB.μ

namespace IdentificationAssumptions

variable {S : UnanchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι} {D : Set ℝ} {ma mb : 𝒳 → ℝ}

/-- **The unanchored identification theorem.** Under `IdentificationAssumptions`:
* `m_a` and `m_b` are conditional mean functions of `Y(a)` and `Y(b)` in the target;
* both are integrable under the target covariate law `Q_X`;
* `∫ m_a dQ_X` is the target mean of `Y(a)`, and so is the density ratio weighted mean
  `E_{P_a}[w_a(X) Y(a)]`; likewise for `b`;
* `∫ m_a dQ_X` and `∫ m_b dQ_X` lie in the domain `D`;
* the target marginal effect of `b` relative to `a` on the scale `g` is the unanchored estimand
  `linkMarginal g Q_X m_a m_b`. -/
theorem identification [IsFiniteMeasure S.sourceA.μ] [IsFiniteMeasure S.sourceB.μ]
    [IsFiniteMeasure S.target.μ] (g : ℝ → ℝ) (h : S.IdentificationAssumptions D ma mb) :
    S.target.IsCondMean S.a ma ∧ S.target.IsCondMean S.b mb ∧
      Integrable ma S.target.covLaw ∧ Integrable mb S.target.covLaw ∧
      ∫ x, ma x ∂S.target.covLaw = S.target.armMean S.a ∧
      ∫ ω, densityRatio S.sourceA.μ S.sourceA.X S.target.μ S.target.X (S.sourceA.X ω) *
          S.sourceA.Y S.a ω ∂S.sourceA.μ = S.target.armMean S.a ∧
      ∫ x, mb x ∂S.target.covLaw = S.target.armMean S.b ∧
      ∫ ω, densityRatio S.sourceB.μ S.sourceB.X S.target.μ S.target.X (S.sourceB.X ω) *
          S.sourceB.Y S.b ω ∂S.sourceB.μ = S.target.armMean S.b ∧
      (∫ x, ma x ∂S.target.covLaw) ∈ D ∧ (∫ x, mb x ∂S.target.covLaw) ∈ D ∧
      S.target.marginalEffect g S.a S.b = linkMarginal g S.target.covLaw ma mb := by
  have ha := integral_covLaw_eq_armMean_of_structurallyInvariant h.measurable_sourceA
    h.measurable_target h.integrable_sourceA h.integrable_target_a h.isCondMean_a
    h.structurallyInvariant_a h.overlap_a
  have hb := integral_covLaw_eq_armMean_of_structurallyInvariant h.measurable_sourceB
    h.measurable_target h.integrable_sourceB h.integrable_target_b h.isCondMean_b
    h.structurallyInvariant_b h.overlap_b
  have wa := armMean_eq_integral_densityRatio_mul h.measurable_sourceA h.measurable_target
    h.overlap_a h.integrable_sourceA h.integrable_target_a h.isCondMean_a
    h.structurallyInvariant_a h.integrable_weighted_a
  have wb := armMean_eq_integral_densityRatio_mul h.measurable_sourceB h.measurable_target
    h.overlap_b h.integrable_sourceB h.integrable_target_b h.isCondMean_b
    h.structurallyInvariant_b h.integrable_weighted_b
  refine ⟨h.isCondMean_a.of_structurallyInvariant h.measurable_sourceA h.measurable_target
      h.structurallyInvariant_a h.overlap_a,
    h.isCondMean_b.of_structurallyInvariant h.measurable_sourceB h.measurable_target
      h.structurallyInvariant_b h.overlap_b, ha.1, hb.1, ha.2, wa.2.symm, hb.2, wb.2.symm,
    ha.2 ▸ h.mem_a, hb.2 ▸ h.mem_b, ?_⟩
  exact S.marginalEffect_target_eq g h.measurable_sourceA h.measurable_sourceB
    h.measurable_target h.integrable_sourceA h.integrable_sourceB h.integrable_target_a
    h.integrable_target_b h.isCondMean_a h.isCondMean_b h.structurallyInvariant_a
    h.structurallyInvariant_b h.overlap_a h.overlap_b

end IdentificationAssumptions

end UnanchoredSetting

/-! ### An omitted prognostic variable -/

section Omitted

variable {Ω₁ Ω₂ 𝒳 𝒲 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲]

/-- **The bias of an arm with an omitted prognostic variable.** Let the full covariate be
`(X, W)` in a source `P` and a target `Q`, with joint laws `P_X ⊗ κ_src` and `Q_X ⊗ κ_*` for
Markov kernels `κ_src`, `κ_*`, and let `m(x, w)` be a conditional mean function of `Y(t)` given
`(X, W)` in both populations (absolute constancy given the full covariate). Adjusting for `X`
alone, the source conditional mean is `m̃(x) = ∫ m(x, ·) dκ_src x`, and its standardized value
`∫ m̃ dQ_X` misses the target mean of `Y(t)` by
`∫ (∫ m(x, ·) dκ_src x - ∫ m(x, ·) dκ_* x) dQ_X`. -/
theorem Population.armMean_omitted_residual {P : Population Ω₁ (𝒳 × 𝒲) ι}
    {Q : Population Ω₂ (𝒳 × 𝒲) ι} [IsFiniteMeasure P.μ] [IsFiniteMeasure Q.μ]
    {κs κt : Kernel 𝒳 𝒲} [IsMarkovKernel κs] [IsMarkovKernel κt] (hXP : Measurable P.X)
    (hXQ : Measurable Q.X) (hlawP : P.covLaw = P.fstCovariate.covLaw ⊗ₘ κs)
    (hlawQ : Q.covLaw = Q.fstCovariate.covLaw ⊗ₘ κt) {t : ι} {m : 𝒳 × 𝒲 → ℝ}
    (hmP : P.IsCondMean t m) (hmQ : Q.IsCondMean t m) (hYP : Integrable (P.Y t) P.μ)
    (hYQ : Integrable (Q.Y t) Q.μ) (hint : Integrable m (Q.fstCovariate.covLaw ⊗ₘ κs)) :
    P.fstCovariate.IsCondMean t (fun x => ∫ w, m (x, w) ∂κs x) ∧
      ∫ x, (∫ w, m (x, w) ∂κs x) ∂Q.fstCovariate.covLaw - Q.armMean t =
        ∫ x, (∫ w, m (x, w) ∂κs x - ∫ w, m (x, w) ∂κt x) ∂Q.fstCovariate.covLaw := by
  have : IsFiniteMeasure Q.fstCovariate.covLaw :=
    Measure.isFiniteMeasure_map (μ := Q.μ) _
  refine ⟨hmP.kernelAverage hXP hlawP hYP, ?_⟩
  have ht : Integrable m (Q.fstCovariate.covLaw ⊗ₘ κt) := hlawQ ▸ hmQ.integrable hXQ
  rw [← integral_kernelAverage_sub_integral_compProd hint ht, ← hlawQ, hmQ.integral_eq hXQ hYQ]

end Omitted

end IndirectComparison

end CausalInference
