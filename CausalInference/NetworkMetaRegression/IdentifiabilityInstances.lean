/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.IdentifiabilityFailures

/-!
# Instances of the identifiability theorems

Concrete data in which every hypothesis of the identifiability theorems holds: the triangle
network `triangleNetArms` (study `0` compares `a = 0` with `c = 2`, study `1` compares `b = 1`
with `c`), the logit link, binary covariate laws `binaryLaw (1/2)` on every arm (full affine
rank, `affineRank_binaryLaw`), and the reference model `triangleModel 0 0 0 0 0 0 0`. Each
instance applies the theorem to this model and an arbitrary second model satisfying the model
hypotheses and reproducing the data, and concludes that the two coincide.

## Main results

* `network_identifiable_of_shared_instance`: individual data on the arms `(0, 2)` and `(0, 0)`
  and aggregate means on all arms identify every model with shared effect modifiers.
* `network_identifiable_of_class_instance`: with each treatment its own class, individual data on
  `(0, 2)`, `(0, 0)` and `(1, 1)` and aggregate means on all arms identify every model.
* `twoStudy_identifiable_instance`: the two study theorem with all three laws `binaryLaw (1/2)`.
* `twoStudy_comparator_instance`: the comparator theorem, without shared effect modifiers.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure NetworkMetaAnalysis MultilevelModel

/-- The arm `(1, 1)` of `b` in the aggregate data study of the triangle network. -/
def triangleNetB : ArmIndex triangleNetArms := ⟨(1, 1), by decide⟩

theorem isProbabilityMeasure_binaryLaw_half : IsProbabilityMeasure (binaryLaw (1 / 2)) :=
  isProbabilityMeasure_binaryLaw ⟨by norm_num, by norm_num⟩

theorem affineRank_binaryLaw_half : AffineRank (binaryLaw (1 / 2)) :=
  affineRank_binaryLaw ⟨by norm_num, by norm_num⟩

/-- **An instance of the network theorem under shared effect modifiers.** In the triangle
network with the logit link and `binaryLaw (1/2)` on every arm, every model `M'` anchored at `c`
with shared effect modifiers whose surfaces agree with those of `triangleModel 0 0 0 0 0 0 0`
on the individual data arms `(0, 2)` and `(0, 0)`, and whose aggregate means agree on every arm,
is that model. -/
theorem network_identifiable_of_shared_instance (M' : MultilevelModel (Fin 2) (Fin 3) 1)
    (hM' : M'.IsAnchoredAt 2) (hS' : M'.SharedEffectModifiers {k | k ≠ 2})
    (ipdr : (triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 2 =ᵐ[binaryLaw (1 / 2)]
      M'.surface Real.sigmoid (M'.μ 0) 2)
    (ipdt : (triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 0 =ᵐ[binaryLaw (1 / 2)]
      M'.surface Real.sigmoid (M'.μ 0) 0)
    (agd : ∀ x : ArmIndex triangleNetArms,
      (triangleModel 0 0 0 0 0 0 0).armMean Real.sigmoid 0 (binaryLaw (1 / 2)) x.1.2 =
        M'.armMean Real.sigmoid (M'.μ x.1.1) (binaryLaw (1 / 2)) x.1.2) :
    triangleModel 0 0 0 0 0 0 0 = M' := by
  have := isProbabilityMeasure_binaryLaw_half
  have hμ : ∀ j, (triangleModel 0 0 0 0 0 0 0).μ j = 0 := fun j => by
    fin_cases j <;> rfl
  exact network_identifiable_of_shared (F := fun _ => binaryLaw (1 / 2)) triangleNetBase_mem
    triangleNet_connected Real.sigmoid_strictMono (triangleModel_anchored _ _ _ _ _ _ _) hM'
    (triangleModel_shared_active _ _ _ _ _ _) hS' triangleNetRef rfl affineRank_binaryLaw_half
    (by rw [hμ]; exact ipdr) triangleNetA (by decide) affineRank_binaryLaw_half
    (by rw [hμ]; exact ipdt) (fun _ _ => integrable_binaryLaw _ _)
    (fun x => by rw [hμ]; exact agd x)

/-- **An instance of the network theorem under class effect modifiers**, with every treatment
its own class (so the class assumption holds for every model): individual data on the arms
`(0, 2)`, `(0, 0)` and `(1, 1)` and aggregate means on every arm of the triangle network, with
the logit link and `binaryLaw (1/2)` on every arm, identify every model anchored at `c`. -/
theorem network_identifiable_of_class_instance (M' : MultilevelModel (Fin 2) (Fin 3) 1)
    (hM' : M'.IsAnchoredAt 2)
    (ipdr : (triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 2 =ᵐ[binaryLaw (1 / 2)]
      M'.surface Real.sigmoid (M'.μ 0) 2)
    (ipda : (triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 0 =ᵐ[binaryLaw (1 / 2)]
      M'.surface Real.sigmoid (M'.μ 0) 0)
    (ipdb : (triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 1 =ᵐ[binaryLaw (1 / 2)]
      M'.surface Real.sigmoid (M'.μ 1) 1)
    (agd : ∀ x : ArmIndex triangleNetArms,
      (triangleModel 0 0 0 0 0 0 0).armMean Real.sigmoid 0 (binaryLaw (1 / 2)) x.1.2 =
        M'.armMean Real.sigmoid (M'.μ x.1.1) (binaryLaw (1 / 2)) x.1.2) :
    triangleModel 0 0 0 0 0 0 0 = M' := by
  have := isProbabilityMeasure_binaryLaw_half
  have hμ : ∀ j, (triangleModel 0 0 0 0 0 0 0).μ j = 0 := fun j => by
    fin_cases j <;> rfl
  have hcls : ∀ N : MultilevelModel (Fin 2) (Fin 3) 1, N.ClassEffectModifiers 2 id :=
    fun N => (classEffectModifiers_iff N 2 id).2 fun k k' _ _ h => by rw [show k = k' from h]
  refine network_identifiable_of_class (F := fun _ => binaryLaw (1 / 2)) (cls := id)
    triangleNetBase_mem triangleNet_connected Real.sigmoid_strictMono
    (triangleModel_anchored _ _ _ _ _ _ _) hM' (hcls _) (hcls _) triangleNetRef rfl
    affineRank_binaryLaw_half (by rw [hμ]; exact ipdr)
    (fun k _ => if k = 0 then triangleNetA else triangleNetB) ?_
    (fun _ _ => affineRank_binaryLaw_half) ?_ (fun _ _ => integrable_binaryLaw _ _)
    (fun x => by rw [hμ]; exact agd x)
  · intro k hk
    fin_cases k
    · decide
    · decide
    · exact absurd rfl hk
  · intro k hk
    fin_cases k
    · simpa [triangleNetA, hμ] using ipda
    · simpa [triangleNetB, hμ] using ipdb
    · exact absurd rfl hk

/-- **An instance of the two study theorem.** With the logit link and `binaryLaw (1/2)` as the
laws of both arms of the individual data study and of the aggregate study, every model `M'`
anchored at `c` with shared effect modifiers of `a` and `b` that reproduces the data of
`triangleModel 0 0 0 0 0 0 0` has its intercepts, prognostic effect, effects and interactions of
`a` and `b`. -/
theorem twoStudy_identifiable_instance (M' : MultilevelModel (Fin 2) (Fin 3) 1)
    (hM' : M'.IsAnchoredAt 2) (hS' : M'.SharedEffectModifiers {0, 1})
    (ipda : (triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 0 =ᵐ[binaryLaw (1 / 2)]
      M'.surface Real.sigmoid (M'.μ 0) 0)
    (ipdc : (triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 2 =ᵐ[binaryLaw (1 / 2)]
      M'.surface Real.sigmoid (M'.μ 0) 2)
    (agdb : (triangleModel 0 0 0 0 0 0 0).armMean Real.sigmoid 0 (binaryLaw (1 / 2)) 1 =
      M'.armMean Real.sigmoid (M'.μ 1) (binaryLaw (1 / 2)) 1)
    (agdc : (triangleModel 0 0 0 0 0 0 0).armMean Real.sigmoid 0 (binaryLaw (1 / 2)) 2 =
      M'.armMean Real.sigmoid (M'.μ 1) (binaryLaw (1 / 2)) 2) :
    0 = M'.μ 0 ∧ 0 = M'.μ 1 ∧ (fun _ => 0) = M'.β₁ ∧ 0 = M'.γ 0 ∧ 0 = M'.γ 1 ∧
      (fun _ => 0) = M'.β₂ 0 ∧ (fun _ => 0) = M'.β₂ 1 := by
  have := isProbabilityMeasure_binaryLaw_half
  exact twoStudy_identifiable (M := triangleModel 0 0 0 0 0 0 0) (jac := 0) (jbc := 1)
    Real.sigmoid_strictMono affineRank_binaryLaw_half affineRank_binaryLaw_half
    (triangleModel_anchored _ _ _ _ _ _ _) hM' ((triangleModel_shared_iff _ _ _ _ _ _ _).2 rfl)
    hS' (fun _ => integrable_binaryLaw _ _) (fun _ => integrable_binaryLaw _ _) ipda ipdc agdb
    agdc

/-- **An instance of the comparator theorem**, with no shared effect modifier assumption: with
the logit link and `binaryLaw (1/2)` on all arms, every model `M'` anchored at `c` that reproduces
the data of `triangleModel 0 0 0 0 0 0 0` has the same marginal log odds ratio of `b` against `a`
in the population of the aggregate study. -/
theorem twoStudy_comparator_instance (M' : MultilevelModel (Fin 2) (Fin 3) 1)
    (hM' : M'.IsAnchoredAt 2)
    (ipda : (triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 0 =ᵐ[binaryLaw (1 / 2)]
      M'.surface Real.sigmoid (M'.μ 0) 0)
    (ipdc : (triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 2 =ᵐ[binaryLaw (1 / 2)]
      M'.surface Real.sigmoid (M'.μ 0) 2)
    (agdb : (triangleModel 0 0 0 0 0 0 0).armMean Real.sigmoid 0 (binaryLaw (1 / 2)) 1 =
      M'.armMean Real.sigmoid (M'.μ 1) (binaryLaw (1 / 2)) 1)
    (agdc : (triangleModel 0 0 0 0 0 0 0).armMean Real.sigmoid 0 (binaryLaw (1 / 2)) 2 =
      M'.armMean Real.sigmoid (M'.μ 1) (binaryLaw (1 / 2)) 2) :
    linkMarginal logit (binaryLaw (1 / 2)) ((triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 0)
        ((triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 1) =
      linkMarginal logit (binaryLaw (1 / 2)) (M'.surface Real.sigmoid (M'.μ 1) 0)
        (M'.surface Real.sigmoid (M'.μ 1) 1) := by
  have := isProbabilityMeasure_binaryLaw_half
  exact twoStudy_comparator_identified (M := triangleModel 0 0 0 0 0 0 0) (jac := 0) (jbc := 1)
    Real.sigmoid_strictMono affineRank_binaryLaw_half affineRank_binaryLaw_half
    (triangleModel_anchored _ _ _ _ _ _ _) hM' (fun _ => integrable_binaryLaw _ _)
    (integrable_binaryLaw _ _) (integrable_binaryLaw _ _) (integrable_binaryLaw _ _) ipda ipdc
    agdb agdc logit

/-- **The hypotheses of the instances hold jointly**: the model `triangleModel 0 0 0 0 0 0 0`
itself satisfies every hypothesis on `M'` of the four instances, so each instance applies to it.
-/
theorem identifiability_instances_apply_to_zero :
    triangleModel 0 0 0 0 0 0 0 = triangleModel 0 0 0 0 0 0 0 ∧
      (0 = (triangleModel 0 0 0 0 0 0 0).μ 0 ∧ 0 = (triangleModel 0 0 0 0 0 0 0).μ 1 ∧
        (fun _ => 0) = (triangleModel 0 0 0 0 0 0 0).β₁ ∧
        0 = (triangleModel 0 0 0 0 0 0 0).γ 0 ∧ 0 = (triangleModel 0 0 0 0 0 0 0).γ 1 ∧
        (fun _ => 0) = (triangleModel 0 0 0 0 0 0 0).β₂ 0 ∧
        (fun _ => 0) = (triangleModel 0 0 0 0 0 0 0).β₂ 1) := by
  have hμ : ∀ j, (triangleModel 0 0 0 0 0 0 0).μ j = 0 := fun j => by
    fin_cases j <;> rfl
  have hagd : ∀ x : ArmIndex triangleNetArms,
      (triangleModel 0 0 0 0 0 0 0).armMean Real.sigmoid 0 (binaryLaw (1 / 2)) x.1.2 =
        (triangleModel 0 0 0 0 0 0 0).armMean Real.sigmoid
          ((triangleModel 0 0 0 0 0 0 0).μ x.1.1) (binaryLaw (1 / 2)) x.1.2 := fun x => by
    rw [hμ]
  have hA := triangleModel_anchored (0 : ℝ) 0 0 0 0 0 0
  refine ⟨network_identifiable_of_shared_instance _ hA
    (triangleModel_shared_active _ _ _ _ _ _) Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
    hagd, twoStudy_identifiable_instance _ hA ((triangleModel_shared_iff _ _ _ _ _ _ _).2 rfl)
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl rfl rfl⟩

/-- The class and comparator instances also apply to `triangleModel 0 0 0 0 0 0 0` itself. -/
theorem identifiability_instances_apply_to_zero' :
    triangleModel 0 0 0 0 0 0 0 = triangleModel 0 0 0 0 0 0 0 ∧
      linkMarginal logit (binaryLaw (1 / 2))
          ((triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 0)
          ((triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid 0 1) =
        linkMarginal logit (binaryLaw (1 / 2))
          ((triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid
            ((triangleModel 0 0 0 0 0 0 0).μ 1) 0)
          ((triangleModel 0 0 0 0 0 0 0).surface Real.sigmoid
            ((triangleModel 0 0 0 0 0 0 0).μ 1) 1) := by
  have hμ : ∀ j, (triangleModel 0 0 0 0 0 0 0).μ j = 0 := fun j => by
    fin_cases j <;> rfl
  have hA := triangleModel_anchored (0 : ℝ) 0 0 0 0 0 0
  refine ⟨network_identifiable_of_class_instance _ hA Filter.EventuallyEq.rfl
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun x => by rw [hμ]),
    twoStudy_comparator_instance _ hA Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl rfl rfl⟩

end NetworkMetaRegression

end CausalInference
