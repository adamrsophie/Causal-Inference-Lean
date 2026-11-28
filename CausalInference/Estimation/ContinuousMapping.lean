/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.ConvergenceInProbability
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# The continuous mapping theorem

A measurable map `g` whose discontinuity set is a null set for the limit preserves convergence in
distribution, in probability (to a random limit) and almost surely. Mathlib has the version for a
continuous `g` (`MeasureTheory.TendstoInDistribution.continuous_comp`); here `g` may be
discontinuous away from the support of the limit, as for `x ↦ x⁻¹` at a nonzero limit.

## Main results

* `preimage_subset_interior_union_discontinuity`: the preimage of an open set lies
  in its interior together with the discontinuity points.
* `MeasureTheory.ProbabilityMeasure.tendsto_map_of_ae_continuousAt`: weak convergence of laws is
  preserved by a measurable map continuous almost everywhere for the limit law.
* `MeasureTheory.TendstoInDistribution.comp_of_ae_continuousAt`: the continuous mapping theorem
  in distribution.
* `MeasureTheory.TendstoInMeasure.comp_of_ae_continuousAt`: in probability, with a random limit.
* `ae_tendsto_comp_of_ae_continuousAt`: almost surely.
* `MeasureTheory.TendstoInMeasure.inv_of_ne_zero`: an instance with a discontinuous map: the
  inverse of a sequence converging in probability to a nonzero constant.

References: P. Billingsley (1999), *Convergence of Probability Measures*, second edition,
Theorem 2.7; A. W. van der Vaart (1998), *Asymptotic Statistics*, Theorem 2.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace CausalInference

/-- The preimage of an open set lies in its interior together with the discontinuity points: at
a continuity point `x` of `g` with `g x ∈ V`, the preimage of `V` is a neighborhood of `x`. -/
theorem preimage_subset_interior_union_discontinuity {E F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] (g : E → F) {V : Set F} (hV : IsOpen V) :
    g ⁻¹' V ⊆ interior (g ⁻¹' V) ∪ {x | ¬ ContinuousAt g x} := by
  intro x hx
  by_cases hc : ContinuousAt g x
  · exact Or.inl (mem_interior_iff_mem_nhds.2 (hc.preimage_mem_nhds (hV.mem_nhds hx)))
  · exact Or.inr hc

/-- **Continuous mapping for weak convergence of laws.** If `μs i → μ` weakly and `g` is
measurable and continuous at `μ`-almost every point, then the image laws converge weakly. For an
open `V`, the preimage `g⁻¹ V` lies in its interior up to the `μ`-null discontinuity set, so
`μ (g⁻¹ V) ≤ liminf μs i (interior (g⁻¹ V)) ≤ liminf μs i (g⁻¹ V)`, and the open set form of the
portmanteau theorem concludes. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.tendsto_map_of_ae_continuousAt
    {E F ι : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E] [HasOuterApproxClosed E] [MeasurableSpace F]
    [TopologicalSpace F] [OpensMeasurableSpace F] {L : Filter ι} [L.IsCountablyGenerated]
    {μ : ProbabilityMeasure E} {μs : ι → ProbabilityMeasure E} (h : Tendsto μs L (𝓝 μ))
    {g : E → F} (hg : Measurable g) (hc : ∀ᵐ x ∂(μ : Measure E), ContinuousAt g x) :
    Tendsto (fun i ↦ (μs i).map g) L (𝓝 (μ.map g)) := by
  refine tendsto_of_forall_isOpen_le_liminf' fun V hV ↦ ?_
  have hD : (μ : Measure E) {x | ¬ ContinuousAt g x} = 0 := ae_iff.1 hc
  calc ((μ.map g : ProbabilityMeasure F) : Measure F) V
      = (μ : Measure E) (g ⁻¹' V) := by
        rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hg hV.measurableSet]
    _ ≤ (μ : Measure E) (interior (g ⁻¹' V)) := by
        refine (measure_mono
          (preimage_subset_interior_union_discontinuity g hV)).trans ?_
        refine (measure_union_le _ _).trans ?_
        rw [hD, add_zero]
    _ ≤ L.liminf fun i ↦ (μs i : Measure E) (interior (g ⁻¹' V)) :=
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto h isOpen_interior
    _ ≤ L.liminf fun i ↦ (((μs i).map g : ProbabilityMeasure F) : Measure F) V := by
        refine liminf_le_liminf (Eventually.of_forall fun i ↦ ?_)
        rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hg hV.measurableSet]
        exact measure_mono interior_subset

/-- **The continuous mapping theorem in distribution.** If `X i → Z` in distribution, `g` is
measurable into a pseudo metrizable space and `g` is continuous at `Z ω` for almost every `ω`,
then `g ∘ X i → g ∘ Z` in distribution. The discontinuity set of `g` is Borel (the continuity set
is a `G_δ`), so the hypothesis transfers to the law of `Z`. -/
theorem _root_.MeasureTheory.TendstoInDistribution.comp_of_ae_continuousAt
    {ι E F Ω' : Type*} {Ω : ι → Type*}
    {m : ∀ i, MeasurableSpace (Ω i)} {μ : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)] [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E] [MeasurableSpace F] [TopologicalSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace.PseudoMetrizableSpace F] {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    {l : Filter ι} [l.IsCountablyGenerated] (h : TendstoInDistribution X l Z μ μ') {g : E → F}
    (hg : Measurable g) (hc : ∀ᵐ ω ∂μ', ContinuousAt g (Z ω)) :
    TendstoInDistribution (fun i ↦ g ∘ X i) l (g ∘ Z) μ μ' where
  forall_aemeasurable i := hg.comp_aemeasurable (h.forall_aemeasurable i)
  aemeasurable_limit := hg.comp_aemeasurable h.aemeasurable_limit
  tendsto := by
    have hc' : ∀ᵐ x ∂(μ'.map Z), ContinuousAt g x :=
      (ae_map_iff h.aemeasurable_limit (IsGδ.setOfPred_continuousAt g).measurableSet).2 hc
    have key := ProbabilityMeasure.tendsto_map_of_ae_continuousAt h.tendsto hg hc'
    have e1 : ∀ i, ProbabilityMeasure.map
        (⟨(μ i).map (X i), inferInstance⟩ : ProbabilityMeasure E) g =
        ⟨(μ i).map (g ∘ X i), inferInstance⟩ := fun i ↦
      Subtype.ext (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable
        (h.forall_aemeasurable i))
    have e2 : ProbabilityMeasure.map
        (⟨μ'.map Z, inferInstance⟩ : ProbabilityMeasure E) g =
        ⟨μ'.map (g ∘ Z), inferInstance⟩ :=
      Subtype.ext (AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h.aemeasurable_limit)
    simp only [e1, e2] at key
    exact key

/-- Mathlib's continuous case `MeasureTheory.TendstoInDistribution.continuous_comp` is the case of
an everywhere continuous `g`. -/
example {E F Ω' : Type*} {Ω : ℕ → Type*} {m : ∀ n, MeasurableSpace (Ω n)}
    {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)] [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] [MeasurableSpace E] [TopologicalSpace E]
    [BorelSpace E] [HasOuterApproxClosed E] [MeasurableSpace F] [TopologicalSpace F]
    [BorelSpace F] [TopologicalSpace.PseudoMetrizableSpace F] {X : (n : ℕ) → Ω n → E}
    {Z : Ω' → E} (h : TendstoInDistribution X atTop Z μ μ') {g : E → F} (hg : Continuous g) :
    TendstoInDistribution (fun n ↦ g ∘ X n) atTop (g ∘ Z) μ μ' :=
  h.comp_of_ae_continuousAt hg.measurable (ae_of_all _ fun _ ↦ hg.continuousAt)

variable {Ω E F : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The continuous mapping theorem almost surely.** If `X n → Y` almost surely and `g` is
continuous at `Y ω` for almost every `ω`, then `g (X n) → g Y` almost surely. No measurability is
needed. -/
theorem ae_tendsto_comp_of_ae_continuousAt [TopologicalSpace E] [TopologicalSpace F]
    {X : ℕ → Ω → E} {Y : Ω → E} {g : E → F}
    (hX : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω)))
    (hc : ∀ᵐ ω ∂P, ContinuousAt g (Y ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ g (X n ω)) atTop (𝓝 (g (Y ω))) := by
  filter_upwards [hX, hc] with ω h1 h2 using h2.tendsto.comp h1

/-- **The continuous mapping theorem in probability.** If `X n → Y` in probability under a finite
measure (the limit may be random), `g` is continuous at `Y ω` for almost every `ω`, and each
`g (X n)` is almost everywhere strongly measurable, then `g (X n) → g Y` in probability. Every
subsequence has a further subsequence along which `X` converges almost surely, the almost sure
form carries it through `g`, and the subsequence criterion concludes. -/
theorem _root_.MeasureTheory.TendstoInMeasure.comp_of_ae_continuousAt
    [IsFiniteMeasure P] [PseudoEMetricSpace E]
    [PseudoEMetricSpace F] {X : ℕ → Ω → E} {Y : Ω → E} (hX : TendstoInMeasure P X atTop Y)
    {g : E → F} (hgX : ∀ n, AEStronglyMeasurable (fun ω ↦ g (X n ω)) P)
    (hc : ∀ᵐ ω ∂P, ContinuousAt g (Y ω)) :
    TendstoInMeasure P (fun n ω ↦ g (X n ω)) atTop (fun ω ↦ g (Y ω)) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff hgX]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (hX.comp_tendsto hns.tendsto_atTop).exists_seq_tendsto_ae
  exact ⟨ns', hns', ae_tendsto_comp_of_ae_continuousAt hae hc⟩

/-- **The continuous mapping theorem in probability, measurable form.** As
`TendstoInMeasure.comp_of_ae_continuousAt` for a measurable `g` into a second countable space
with the Borel σ-algebra and almost everywhere measurable `X n`. -/
theorem _root_.MeasureTheory.TendstoInMeasure.comp_of_ae_continuousAt_of_measurable
    [IsFiniteMeasure P]
    [PseudoEMetricSpace E] [MeasurableSpace E] [PseudoEMetricSpace F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] {X : ℕ → Ω → E} {Y : Ω → E}
    (hX : TendstoInMeasure P X atTop Y) (hXm : ∀ n, AEMeasurable (X n) P) {g : E → F}
    (hg : Measurable g) (hc : ∀ᵐ ω ∂P, ContinuousAt g (Y ω)) :
    TendstoInMeasure P (fun n ω ↦ g (X n ω)) atTop (fun ω ↦ g (Y ω)) :=
  hX.comp_of_ae_continuousAt (fun n ↦ (hg.comp_aemeasurable (hXm n)).aestronglyMeasurable) hc

/-- **Instance with a discontinuous map: inverses.** If real `X n → c ≠ 0` in probability under a
finite measure and each `X n` is almost everywhere measurable, then `(X n)⁻¹ → c⁻¹` in
probability. The map `x ↦ x⁻¹` is measurable and discontinuous at `0`, which the constant limit
avoids. -/
theorem _root_.MeasureTheory.TendstoInMeasure.inv_of_ne_zero
    [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} {c : ℝ}
    (hX : TendstoInMeasure P X atTop (fun _ ↦ c)) (hXm : ∀ n, AEMeasurable (X n) P)
    (hc : c ≠ 0) :
    TendstoInMeasure P (fun n ω ↦ (X n ω)⁻¹) atTop (fun _ ↦ c⁻¹) :=
  hX.comp_of_ae_continuousAt_of_measurable hXm measurable_inv
    (ae_of_all _ fun _ ↦ continuousAt_inv₀ hc)

end CausalInference
