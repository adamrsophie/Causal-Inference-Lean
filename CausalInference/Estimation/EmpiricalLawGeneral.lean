/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.EmpiricalLawMonteCarlo

/-!
# Almost sure weak convergence of the empirical law on a second countable space

Draws `D₀, D₁, ...` are i.i.d. under `P` with law `μ = P.map D₀` and take values in a topological
space `𝒪` with a countable basis, whose σ-algebra contains the open sets and the singletons.
Almost surely the empirical laws `μ̂_{M+1}` of the first `M + 1` draws converge weakly to `μ`.

Every separable metrizable space with its Borel σ-algebra satisfies these conditions (a separable
metrizable space has a countable basis, and it is Hausdorff, so its points are closed); so do
`ℝ`, `EuclideanSpace ℝ (Fin d)` and `Fin d → ℝ`. No metric is used in the proof.

The proof runs the strong law simultaneously over the countable family of finite unions of basis
sets. On the resulting almost sure event, every open set `G` is the increasing union of the
finite unions of basis sets contained in `G`, so `μ(G) ≤ liminf μ̂_M(G)`, and the open set form
of the portmanteau theorem concludes.

## Main definitions

* `EmpiricalLaw.basisUnion`: the union of a finite family of basis sets.

## Main results

* `EmpiricalLaw.tendsto_ae_empiricalMeasure_of_secondCountable`: the general statement.
* `EmpiricalLaw.tendsto_ae_empiricalMeasure_real_of_secondCountable`: the real line as a special
  case.
* `EmpiricalLaw.ae_data_tendsto_ae_empiricalMeasure_of_secondCountable`: the same for a family
  of posterior laws indexed by the data, for almost every data value.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace CausalInference

namespace EmpiricalLaw

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [TopologicalSpace 𝒪] [SecondCountableTopology 𝒪]

/-- The union of a finite family `T` of sets of the countable basis of `𝒪`. -/
def basisUnion (T : Finset (countableBasis 𝒪)) : Set 𝒪 := ⋃ b ∈ T, (b : Set 𝒪)

lemma isOpen_basisUnion (T : Finset (countableBasis 𝒪)) : IsOpen (basisUnion T) :=
  isOpen_biUnion fun b _ ↦ (isBasis_countableBasis 𝒪).isOpen b.2

/-- Every open set is the union of the finite unions of basis sets it contains. -/
lemma iUnion_basisUnion_filter {G : Set 𝒪} (hG : IsOpen G) :
    open Classical in
    ⋃ T : Finset (countableBasis 𝒪), basisUnion (T.filter fun b ↦ (b : Set 𝒪) ⊆ G) = G := by
  classical
  refine Subset.antisymm (iUnion_subset fun T ↦ iUnion₂_subset fun b hb ↦ ?_) fun x hx ↦ ?_
  · exact (Finset.mem_filter.1 hb).2
  · obtain ⟨v, hv, hxv, hvG⟩ := (isBasis_countableBasis 𝒪).exists_subset_of_mem_open hx hG
    refine mem_iUnion.2 ⟨{⟨v, hv⟩}, mem_iUnion₂.2 ⟨⟨v, hv⟩, ?_, hxv⟩⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_singleton_self _, hvG⟩

variable [MeasurableSpace 𝒪] [OpensMeasurableSpace 𝒪] [MeasurableSingletonClass 𝒪]

/-- **Almost sure weak convergence of the empirical law.** Let `𝒪` be a topological space with a
countable basis, whose σ-algebra contains the open sets and the singletons (for instance a
separable metrizable space with its Borel σ-algebra). For i.i.d. draws with law `μ = P.map D₀`,
almost surely the empirical laws `μ̂_{M+1}` of the first `M + 1` draws converge to `μ` in the
topology of weak convergence of probability measures. -/
theorem tendsto_ae_empiricalMeasure_of_secondCountable [IsProbabilityMeasure P]
    {D : ℕ → Ω → 𝒪} (hD : IsIIDSample D P) :
    ∀ᵐ ω ∂P, Tendsto (β := ProbabilityMeasure 𝒪) (fun n : ℕ ↦
        (⟨empiricalMeasure D (n + 1) ω, inferInstance⟩ : ProbabilityMeasure 𝒪)) atTop
      (𝓝 (⟨P.map (D 0), (Measure.isProbabilityMeasure_map_iff
        (hD.ident 0).aemeasurable_fst).2 inferInstance⟩ : ProbabilityMeasure 𝒪)) := by
  classical
  have : Countable (countableBasis 𝒪) := (countable_countableBasis 𝒪).to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ T : Finset (countableBasis 𝒪),
      Tendsto (fun n ↦ (empiricalMeasure D n ω).real (basisUnion T)) atTop
        (𝓝 ((P.map (D 0)).real (basisUnion T))) :=
    ae_all_iff.2 fun T ↦ tendsto_ae_empiricalMeasure_real hD (isOpen_basisUnion T).measurableSet
  have : IsProbabilityMeasure (P.map (D 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hD.ident 0).aemeasurable_fst).2 inferInstance
  filter_upwards [hall] with ω hω
  refine tendsto_of_forall_isOpen_le_liminf_nat' fun G hG ↦ ?_
  simp only [ProbabilityMeasure.coe_mk]
  set s : Finset (countableBasis 𝒪) → Set 𝒪 :=
    fun T ↦ basisUnion (T.filter fun b ↦ (b : Set 𝒪) ⊆ G) with hs
  have hmono : Monotone s := fun T T' hT ↦ iUnion₂_subset fun b hb ↦
    Finset.subset_set_biUnion_of_mem (f := fun b : countableBasis 𝒪 ↦ (b : Set 𝒪))
      (Finset.filter_subset_filter _ hT hb)
  have hsub : ∀ T, s T ⊆ G := fun T ↦ iUnion₂_subset fun b hb ↦ (Finset.mem_filter.1 hb).2
  have hG' := iUnion_basisUnion_filter hG
  calc P.map (D 0) G = P.map (D 0) (⋃ T, s T) := by rw [hG']
    _ = ⨆ T, P.map (D 0) (s T) := hmono.measure_iUnion
    _ ≤ _ := iSup_le fun T ↦ ?_
  have hT : Tendsto (fun n : ℕ ↦ empiricalMeasure D (n + 1) ω (s T)) atTop
      (𝓝 (P.map (D 0) (s T))) := by
    have h1 := (ENNReal.tendsto_ofReal
      ((hω (T.filter fun b ↦ (b : Set 𝒪) ⊆ G)).comp (tendsto_add_atTop_nat 1)))
    rw [ofReal_measureReal (measure_ne_top _ _)] at h1
    refine h1.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    exact ofReal_measureReal (measure_ne_top _ _)
  rw [← hT.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n ↦ measure_mono (hsub T))

/-- **Weak convergence for almost every data value.** If for `ρ` almost every data value `x` the
draws `D x` are i.i.d. under `P` with law the posterior `Q x` on a second countable space, then
for `ρ` almost every `x`, almost surely the empirical laws converge weakly to `Q x`. -/
theorem ae_data_tendsto_ae_empiricalMeasure_of_secondCountable [IsProbabilityMeasure P]
    {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {ρ : Measure 𝒳} {Q : 𝒳 → Measure 𝒪}
    [∀ x, IsProbabilityMeasure (Q x)] {D : 𝒳 → ℕ → Ω → 𝒪}
    (hD : ∀ᵐ x ∂ρ, IsIIDSample (D x) P ∧ P.map (D x 0) = Q x) :
    ∀ᵐ x ∂ρ, ∀ᵐ ω ∂P, Tendsto (β := ProbabilityMeasure 𝒪) (fun n : ℕ ↦
        (⟨empiricalMeasure (D x) (n + 1) ω, inferInstance⟩ : ProbabilityMeasure 𝒪)) atTop
      (𝓝 (⟨Q x, inferInstance⟩ : ProbabilityMeasure 𝒪)) := by
  filter_upwards [hD] with x ⟨hx, hQ⟩
  have hQ' : (⟨Q x, inferInstance⟩ : ProbabilityMeasure 𝒪) =
      ⟨P.map (D x 0), (Measure.isProbabilityMeasure_map_iff
        (hx.ident 0).aemeasurable_fst).2 inferInstance⟩ := Subtype.ext hQ.symm
  rw [hQ']
  exact tendsto_ae_empiricalMeasure_of_secondCountable hx

end EmpiricalLaw

/-- **The real line as a special case.** For i.i.d. real draws, almost surely the empirical laws
converge weakly to the law of the draws. -/
theorem EmpiricalLaw.tendsto_ae_empiricalMeasure_real_of_secondCountable {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {D : ℕ → Ω → ℝ}
    (hD : IsIIDSample D P) :
    ∀ᵐ ω ∂P, Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ ↦
        (⟨empiricalMeasure D (n + 1) ω, inferInstance⟩ : ProbabilityMeasure ℝ)) atTop
      (𝓝 (⟨P.map (D 0), (Measure.isProbabilityMeasure_map_iff
        (hD.ident 0).aemeasurable_fst).2 inferInstance⟩ : ProbabilityMeasure ℝ)) :=
  EmpiricalLaw.tendsto_ae_empiricalMeasure_of_secondCountable hD

end CausalInference
