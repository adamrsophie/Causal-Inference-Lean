/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.EntropyExistence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The entropy balancing weights are a measurable function of the data

The entropy balancing weights `balancingWeights Δ` of the centered features `Δᵢ = φ(xᵢ) - t` are
built from a dual minimizer chosen by `Classical.choose` (`dualMinimizer`). The chosen minimizer
is not shown to be measurable here; the **weights** are, because they do not depend on the choice
(`entropyWeights_eq_balancingWeights`):

* on the feasible set, where some `β` solves the balance equation `∑ᵢ exp(βᵀΔᵢ) Δᵢ = 0`, the
  weights are `entropyWeights Δ β` for every such `β` (`balancingWeights_of_momentBalanced`);
* off it, the weights are the uniform weights `1 / n` (`balancingWeights_of_not_exists`).

The set of pairs `(Δ, β)` solving the balance equation is closed, so the preimage of a closed set
of weight vectors is the projection of a closed subset of a Euclidean space, together with a
piece of the complement of such a projection. Projections of closed subsets of a σ-compact space
are σ-compact, hence Borel (`measurableSet_image_fst_of_isClosed`). This gives
`measurable_balancingWeights`, and the joint measurability in the target moments and the sample,
`measurable_balancingWeights_features`.

## Main results

* `balancingWeights_of_momentBalanced`, `balancingWeights_of_not_exists`.
* `measurable_balancingWeights`: `Δ ↦ balancingWeights Δ` is Borel measurable.
* `measurable_balancingWeights_features`: `(t, x) ↦ balancingWeights (fun i => φ (x i) - t)` is
  measurable for a measurable feature map `φ`.

## References

* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

open MeasureTheory Finset

namespace CausalInference

namespace PopulationAdjustment

/-- A σ-compact subset of a Hausdorff space with a Borel σ-algebra is measurable. -/
theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {s : Set X} (hs : IsSigmaCompact s) :
    MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

/-- The projection of a closed subset of a σ-compact product is measurable: it is
σ-compact. -/
theorem measurableSet_image_fst_of_isClosed {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y]
    [SigmaCompactSpace (X × Y)] {C : Set (X × Y)} (hC : IsClosed C) :
    MeasurableSet (Prod.fst '' C) :=
  measurableSet_of_isSigmaCompact
    ((isSigmaCompact_univ.of_isClosed_subset hC (Set.subset_univ _)).image continuous_fst)

variable {ι : Type*} [Fintype ι] {p : ℕ}

/-- **On the feasible set the weights are those of any balancing parameter**: if `β` solves
`∑ᵢ exp(βᵀΔᵢ) Δᵢ = 0`, then `balancingWeights Δ = entropyWeights Δ β`. -/
theorem balancingWeights_of_momentBalanced [Nonempty ι] {Δ : ι → Fin p → ℝ} {β : Fin p → ℝ}
    (hβ : MomentBalanced (fun i => Real.exp (β ⬝ᵥ Δ i)) Δ 0) :
    balancingWeights Δ = entropyWeights Δ β :=
  (entropyWeights_eq_balancingWeights ((isMinOn_logPartition_iff β).2 hβ)).symm

/-- **Off the feasible set the weights are uniform**: if no `β` solves the balance equation,
`balancingWeights Δ = entropyWeights Δ 0`, the weights `1 / n`. -/
theorem balancingWeights_of_not_exists [Nonempty ι] {Δ : ι → Fin p → ℝ}
    (h : ¬ ∃ β, MomentBalanced (fun i => Real.exp (β ⬝ᵥ Δ i)) Δ 0) :
    balancingWeights Δ = entropyWeights Δ 0 := by
  have hex : ¬ ∃ β, IsMinOn (logPartition Δ) Set.univ β := fun ⟨β, hβ⟩ =>
    h ⟨β, (isMinOn_logPartition_iff β).1 hβ⟩
  simp only [balancingWeights, dualMinimizer, hex, ↓reduceDIte]

/-- The entropy weights are jointly continuous in the centered features and the parameter. -/
theorem continuous_entropyWeights [Nonempty ι] :
    Continuous fun q : (ι → Fin p → ℝ) × (Fin p → ℝ) => entropyWeights q.1 q.2 := by
  have hE : ∀ i : ι, Continuous fun q : (ι → Fin p → ℝ) × (Fin p → ℝ) =>
      Real.exp (q.2 ⬝ᵥ q.1 i) := fun i =>
    Real.continuous_exp.comp (continuous_snd.dotProduct ((continuous_apply i).comp continuous_fst))
  have hZ : Continuous fun q : (ι → Fin p → ℝ) × (Fin p → ℝ) => partitionFunction q.1 q.2 :=
    continuous_finsetSum _ fun j _ => hE j
  exact continuous_pi fun i =>
    (hE i).div hZ fun q => (partitionFunction_pos (Δ := q.1) q.2).ne'

/-- **The entropy balancing weights are a Borel measurable function of the centered
features.** -/
theorem measurable_balancingWeights :
    Measurable (balancingWeights : (ι → Fin p → ℝ) → ι → ℝ) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact measurable_of_subsingleton_codomain _
  set Bal := {q : (ι → Fin p → ℝ) × (Fin p → ℝ) |
    MomentBalanced (fun i => Real.exp (q.2 ⬝ᵥ q.1 i)) q.1 0} with hBaldef
  have hBal : IsClosed Bal := by
    refine isClosed_eq (continuous_finsetSum _ fun i _ => ?_) continuous_const
    exact (Real.continuous_exp.comp (continuous_snd.dotProduct
      ((continuous_apply i).comp continuous_fst))).smul
      (((continuous_apply i).comp continuous_fst).sub continuous_const)
  refine measurable_of_isClosed fun U hU => ?_
  have hT : IsClosed (Bal ∩ (fun q => entropyWeights q.1 q.2) ⁻¹' U) :=
    hBal.inter (hU.preimage continuous_entropyWeights)
  have heq : balancingWeights ⁻¹' U =
      Prod.fst '' (Bal ∩ (fun q => entropyWeights q.1 q.2) ⁻¹' U) ∪
        ((Prod.fst '' Bal)ᶜ ∩ {Δ | entropyWeights Δ 0 ∈ U}) := by
    ext Δ
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_ofPred_eq, hBaldef]
    by_cases h : ∃ β, MomentBalanced (fun i => Real.exp (β ⬝ᵥ Δ i)) Δ 0
    · obtain ⟨β, hβ⟩ := h
      rw [balancingWeights_of_momentBalanced hβ]
      constructor
      · intro hw; exact Or.inl ⟨(Δ, β), ⟨hβ, hw⟩, rfl⟩
      · rintro (⟨⟨Δ', β'⟩, ⟨hβ', hw⟩, rfl⟩ | ⟨hn', -⟩)
        · have h := (balancingWeights_of_momentBalanced hβ).symm.trans
            (balancingWeights_of_momentBalanced hβ')
          rw [h]; exact hw
        · exact (hn' ⟨(Δ, β), hβ, rfl⟩).elim
    · rw [balancingWeights_of_not_exists h]
      constructor
      · intro hw
        refine Or.inr ⟨?_, hw⟩
        rintro ⟨q, hq, hq1⟩
        exact h ⟨q.2, hq1 ▸ hq⟩
      · rintro (⟨q, ⟨hq, -⟩, hq1⟩ | ⟨-, hw⟩)
        · exact (h ⟨q.2, hq1 ▸ hq⟩).elim
        · exact hw
  rw [heq]
  refine (measurableSet_image_fst_of_isClosed hT).union
    ((measurableSet_image_fst_of_isClosed hBal).compl.inter ?_)
  exact (continuous_entropyWeights.comp (continuous_id.prodMk continuous_const)).measurable
    hU.measurableSet

/-- **The entropy balancing weights are jointly measurable in the target moments and the
sample.** For a measurable feature map `φ`, the map
`(t, x) ↦ balancingWeights (fun i => φ (x i) - t)` is measurable. -/
theorem measurable_balancingWeights_features {𝒳 : Type*} [MeasurableSpace 𝒳]
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) :
    Measurable fun q : (Fin p → ℝ) × (ι → 𝒳) => balancingWeights fun i => φ (q.2 i) - q.1 := by
  have h : Measurable fun q : (Fin p → ℝ) × (ι → 𝒳) => fun i => φ (q.2 i) - q.1 :=
    Measurable.of_eval fun i =>
      (hφ.comp ((measurable_pi_apply i).comp measurable_snd)).sub measurable_fst
  exact measurable_balancingWeights.comp h

/-- For fixed target moments `t`, the entropy balancing weights of the sample `x` are a
measurable function of `x`. -/
theorem measurable_balancingWeights_sample {𝒳 : Type*} [MeasurableSpace 𝒳]
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) (t : Fin p → ℝ) :
    Measurable fun x : ι → 𝒳 => balancingWeights fun i => φ (x i) - t := by
  have h : Measurable fun x : ι → 𝒳 => fun i => φ (x i) - t :=
    Measurable.of_eval fun i => (hφ.comp (measurable_pi_apply i)).sub_const t
  exact measurable_balancingWeights.comp h

end PopulationAdjustment

end CausalInference
