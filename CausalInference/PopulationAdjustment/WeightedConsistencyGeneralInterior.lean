/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyContrast
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# The interior condition and the margin condition for entropy balancing weights

Let `ν` be the law of the features `φ(X)` on `ℝ^p` (sup norm) and `t` the reported target
moments. The consistency theory of the weighted (matching adjusted) estimator in
`WeightedConsistencyFeasible` and `WeightedConsistencyArm` assumes the **margin condition**: there
is `δ > 0` with `ν{y | δ ≤ vᵀ(y - t)} ≥ δ` for every direction `v` of norm one. This file shows
that it is exactly the usual **interior condition**: `t` lies in the interior of the closed convex
hull `C` of the support of `ν`.

* If `t ∈ interior C`, every direction `v ≠ 0` carries positive mass strictly beyond `t`:
  otherwise the closed half space `{vᵀ(y - t) ≤ 0}` has full measure, contains the support and
  hence `C`, and `t` lies on its boundary (`measure_pos_of_mem_interior_closedConvexHull`).
* Positive mass in every direction gives a uniform margin: `v ↦ ∫ min 1 (max 0 (vᵀ(y - t))) dν`
  is continuous (dominated convergence) and positive on the compact unit sphere, so it has a
  positive minimum `m`, and `δ = m / 2` works (`exists_margin_of_measure_pos`).
* Conversely, under the margin condition every `y ∉ C` is strictly separated from `C` by a
  hyperplane; the margin in the direction of its normal puts a point of the support at distance
  at least `δ` beyond `t`, which forces `‖y - t‖ > δ / p`. So the ball of radius `δ / p` around
  `t` lies in `C` (`mem_interior_closedConvexHull_of_margin`).

**The lower dimensional case.** If the support lies in a proper affine subspace (the features are
linearly dependent up to a constant), `C` has empty interior and the margin condition fails for
every `δ > 0` (`not_margin_of_affineSpan_ne_top`). The natural replacement is the intrinsic
interior of `C` relative to the affine span of the support. There the entropy balancing weights
are still unique (`EntropyUniqueness`) but the dual parameter is not: adding a direction
orthogonal to all centered sample features leaves the dual objective unchanged
(`logPartition_add_of_dotProduct_eq_zero`). The consistency theorems then apply after
reparametrizing the features by coordinates of the affine span, which this file does not carry
out.

The consistency theorems of `WeightedConsistencyArm` and `WeightedConsistencyContrast` are
restated under the interior condition (`sampleBalancedArmMean_isConsistent_of_interior` and the
contrasts).

## Main results

* `measure_pos_of_mem_interior_closedConvexHull`, `exists_margin_of_measure_pos`,
  `mem_interior_closedConvexHull_of_margin`.
* `mem_interior_closedConvexHull_iff_margin`, `mem_interior_closedConvexHull_iff_measure_pos`.
* `not_margin_of_affineSpan_ne_top`, `logPartition_add_of_dotProduct_eq_zero`.
* `exists_margin_of_mem_interior_map`: the margin condition for a feature map of records.
* `sampleBalancedArmMean_isConsistent_of_interior`,
  `sampleBalancedArmMean_isConsistent_armMean_of_interior`,
  `sampleBalancedArmMean_isConsistent_trial_of_interior`,
  `unanchoredBalancedEstimate_isConsistent_of_interior`,
  `anchoredBalancedEstimate_isConsistent_of_interior`,
  `anchoredBalancedEstimate_isConsistent_identity_of_interior`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press (1970).
* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

section Convex

variable {p : ℕ}

/-- A linear functional on `ℝ^p` is a dot product: `f y = wᵀy` with `wₖ = f(eₖ)`. -/
theorem exists_dotProduct_eq_of_strongDual (f : StrongDual ℝ (Fin p → ℝ)) :
    ∃ w : Fin p → ℝ, ∀ y, f y = w ⬝ᵥ y := by
  refine ⟨fun k => f (fun j => if k = j then 1 else 0), fun y => ?_⟩
  rw [show f y = (f : (Fin p → ℝ) →ₗ[ℝ] ℝ) y from rfl, LinearMap.pi_apply_eq_sum_univ, dotProduct]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul, mul_comm]; rfl

/-- The clamp `min 1 (max 0 s)` used to test positive mass. -/
theorem unitClamp_le_one (s : ℝ) : min 1 (max 0 s) ≤ 1 := min_le_left _ _

theorem unitClamp_nonneg (s : ℝ) : 0 ≤ min 1 (max 0 s) := le_min zero_le_one (le_max_left _ _)

theorem le_of_le_unitClamp {s c : ℝ} (hc : 0 < c) (h : c ≤ min 1 (max 0 s)) : c ≤ s := by
  have h1 := h.trans (min_le_right _ _)
  rcases le_total 0 s with hs | hs
  · rwa [max_eq_right hs] at h1
  · rw [max_eq_left hs] at h1; linarith

variable {ν : Measure (Fin p → ℝ)} [IsProbabilityMeasure ν] {t : Fin p → ℝ}

omit [IsProbabilityMeasure ν] in
/-- **The interior condition gives positive mass beyond the target in every direction.** If `t`
lies in the interior of the closed convex hull of the support of `ν`, then for every `v ≠ 0`,
`ν{y | 0 < vᵀ(y - t)} > 0`. Otherwise the closed half space `{vᵀ(y - t) ≤ 0}` has full measure,
so it contains the support and the closed convex hull, while it does not contain the points
`t + ε v`, `ε > 0`, which tend to `t`. -/
theorem measure_pos_of_mem_interior_closedConvexHull
    (ht : t ∈ interior (closedConvexHull ℝ ν.support)) {v : Fin p → ℝ} (hv : v ≠ 0) :
    0 < ν {y | 0 < v ⬝ᵥ (y - t)} := by
  by_contra h0
  rw [not_lt, nonpos_iff_eq_zero] at h0
  set H : Set (Fin p → ℝ) := {y | v ⬝ᵥ (y - t) ≤ 0} with hH
  have hHc : IsClosed H :=
    isClosed_le ((continuous_const.dotProduct (continuous_id.sub continuous_const)))
      continuous_const
  have hHv : Convex ℝ H := by
    have : H = (fun y => v ⬝ᵥ (y - t)) ⁻¹' Set.Iic 0 := rfl
    intro x hx y hy a b ha hb hab
    simp only [hH, Set.mem_ofPred_eq] at hx hy ⊢
    have : a • x + b • y - t = a • (x - t) + b • (y - t) := by
      funext k
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (t k) * hab
    rw [this, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    nlinarith
  have hae : H ∈ ae ν := by
    rw [mem_ae_iff]
    convert h0 using 2
    ext y; simp [hH]
  have hsub : closedConvexHull ℝ ν.support ⊆ H :=
    closedConvexHull_min (Measure.support_subset_of_isClosed hHc hae) hHv hHc
  have hint : interior (closedConvexHull ℝ ν.support) ∈ 𝓝 t := isOpen_interior.mem_nhds ht
  have htend : Tendsto (fun ε : ℝ => t + ε • v) (𝓝[>] 0) (𝓝 t) := by
    have : Tendsto (fun ε : ℝ => t + ε • v) (𝓝 0) (𝓝 (t + (0 : ℝ) • v)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hεint, hε⟩ := ((htend.eventually_mem hint).and self_mem_nhdsWithin).exists
  have hmem : t + ε • v ∈ H := hsub (interior_subset hεint)
  simp only [hH, Set.mem_ofPred_eq, add_sub_cancel_left, dotProduct_smul, smul_eq_mul] at hmem
  have hvv : 0 < v ⬝ᵥ v := by
    have h0' : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun k _ => mul_self_nonneg _
    exact lt_of_le_of_ne h0' fun h => hv (dotProduct_self_eq_zero.1 h.symm)
  have : (0 : ℝ) < ε := hε
  nlinarith

/-- **Positive mass in every direction gives a uniform margin.** If every direction `v` of norm
one carries positive mass beyond `t`, `ν{y | 0 < vᵀ(y - t)} > 0`, then there is `δ > 0` with
`ν{y | δ ≤ vᵀ(y - t)} ≥ δ` for every such `v`. The map `v ↦ ∫ min 1 (max 0 (vᵀ(y - t))) dν` is
continuous by dominated convergence and positive on the compact unit sphere; half of its minimum
is a margin. -/
theorem exists_margin_of_measure_pos
    (h : ∀ v : Fin p → ℝ, ‖v‖ = 1 → 0 < ν {y | 0 < v ⬝ᵥ (y - t)}) :
    ∃ δ, 0 < δ ∧ ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {y | δ ≤ v ⬝ᵥ (y - t)} := by
  set F : (Fin p → ℝ) → ℝ := fun v => ∫ y, min 1 (max 0 (v ⬝ᵥ (y - t))) ∂ν with hF
  have hmeas : ∀ v : Fin p → ℝ, Measurable fun y : Fin p → ℝ => min 1 (max 0 (v ⬝ᵥ (y - t))) :=
    fun v => (by fun_prop : Continuous fun y : Fin p → ℝ =>
      min 1 (max 0 (v ⬝ᵥ (y - t)))).measurable
  have hint : ∀ v : Fin p → ℝ, Integrable (fun y => min 1 (max 0 (v ⬝ᵥ (y - t)))) ν := fun v =>
    (integrable_const (1 : ℝ)).mono' (hmeas v).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (unitClamp_nonneg _)]; exact unitClamp_le_one _)
  have hFc : Continuous F := by
    refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
      (fun v => (hmeas v).aestronglyMeasurable)
      (fun v => ae_of_all _ fun y => ?_) (integrable_const _) (ae_of_all _ fun y => by fun_prop)
    rw [Real.norm_eq_abs, abs_of_nonneg (unitClamp_nonneg _)]; exact unitClamp_le_one _
  have hFpos : ∀ v : Fin p → ℝ, ‖v‖ = 1 → 0 < F v := by
    intro v hv
    rw [hF, integral_pos_iff_support_of_nonneg (fun y => unitClamp_nonneg _) (hint v)]
    refine (h v hv).trans_le (measure_mono fun y hy => ?_)
    simp only [Set.mem_ofPred_eq] at hy
    simp only [Function.mem_support]
    exact (lt_min one_pos (lt_max_of_lt_right hy)).ne'
  rcases (Metric.sphere (0 : Fin p → ℝ) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun v hv => ?_⟩
    have : v ∈ Metric.sphere (0 : Fin p → ℝ) 1 := by simpa using hv
    rw [hS] at this; exact absurd this (Set.notMem_empty v)
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : Fin p → ℝ) 1).exists_isMinOn hS
    hFc.continuousOn
  have hv₀1 : ‖v₀‖ = 1 := by simpa using hv₀
  set m := F v₀ with hm
  have hm0 : 0 < m := hFpos v₀ hv₀1
  refine ⟨m / 2, half_pos hm0, fun v hv => ?_⟩
  have hmv : m ≤ F v := hmin (by simpa using hv)
  set g : (Fin p → ℝ) → ℝ := fun y => min 1 (max 0 (v ⬝ᵥ (y - t))) with hg
  have hset : MeasurableSet {y : Fin p → ℝ | m / 2 ≤ g y} :=
    measurableSet_le measurable_const (hmeas v)
  have hpt : ∀ y, g y ≤ Set.indicator {y | m / 2 ≤ g y} (fun _ => (1 : ℝ)) y + m / 2 := by
    intro y
    by_cases hy : m / 2 ≤ g y
    · rw [Set.indicator_of_mem hy]; linarith [unitClamp_le_one (v ⬝ᵥ (y - t))]
    · rw [Set.indicator_of_notMem hy]; linarith
  have hle : F v ≤ ν.real {y | m / 2 ≤ g y} + m / 2 := by
    calc F v ≤ ∫ y, (Set.indicator {y | m / 2 ≤ g y} (fun _ => (1 : ℝ)) y + m / 2) ∂ν :=
          integral_mono (hint v) (((integrable_const (1 : ℝ)).indicator hset).add
            (integrable_const _)) hpt
      _ = ν.real {y | m / 2 ≤ g y} + m / 2 := by
          rw [integral_add ((integrable_const (1 : ℝ)).indicator hset) (integrable_const _),
            ← Pi.one_def, integral_indicator_one hset, integral_const, probReal_univ, one_smul]
  have hmono : ν.real {y | m / 2 ≤ g y} ≤ ν.real {y | m / 2 ≤ v ⬝ᵥ (y - t)} :=
    measureReal_mono fun y hy => le_of_le_unitClamp (half_pos hm0) hy
  linarith

/-- **The margin condition puts the target in the interior.** If `δ > 0` and
`ν{y | δ ≤ vᵀ(y - t)} ≥ δ` for every `v` of norm one, then `t` lies in the interior of the closed
convex hull `C` of the support of `ν`: a point `y ∉ C` is strictly separated from `C` by a
hyperplane with normal `w`; the margin in the direction `-w / ‖w‖` gives a point of the support
beyond `t`, so `‖y - t‖ > δ / p`, and the ball of radius `δ / p` around `t` lies in `C`. -/
theorem mem_interior_closedConvexHull_of_margin {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {y | δ ≤ v ⬝ᵥ (y - t)}) :
    t ∈ interior (closedConvexHull ℝ ν.support) := by
  set C := closedConvexHull ℝ ν.support with hC
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    have hne : ν.support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero ν)
    obtain ⟨y, hy⟩ := hne
    have : C = Set.univ := by
      refine Set.eq_univ_of_forall fun z => ?_
      rw [Subsingleton.elim z y]; exact subset_closedConvexHull hy
    rw [this, interior_univ]; exact Set.mem_univ t
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Metric.ball_mem_nhds t
    (div_pos hδ hp')) fun y hy => ?_)
  by_contra hyC
  obtain ⟨f, u, hfy, hfC⟩ := geometric_hahn_banach_point_closed (convex_closedConvexHull)
    (isClosed_closedConvexHull) hyC
  obtain ⟨w, hw⟩ := exists_dotProduct_eq_of_strongDual f
  -- the support meets every half space of positive measure
  have hsupp : ∀ v : Fin p → ℝ, ‖v‖ = 1 → ∃ z ∈ C, δ ≤ v ⬝ᵥ (z - t) := fun v hv => by
    have hpos : 0 < ν {y | δ ≤ v ⬝ᵥ (y - t)} := by
      have := (h v hv)
      rw [measureReal_def] at this
      exact ENNReal.toReal_pos_iff.1 (hδ.trans_le this) |>.1
    obtain ⟨z, hz, hzs⟩ := Measure.nonempty_inter_support_of_pos hpos
    exact ⟨z, subset_closedConvexHull hzs, hz⟩
  have hw0 : w ≠ 0 := by
    intro hw0
    have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    obtain ⟨z, hzC, -⟩ := hsupp (fun _ => 1) (by
      rw [pi_norm_const (1 : ℝ)]; simp)
    have h1 := hfC z hzC
    have h2 := hfy
    rw [hw] at h1 h2
    rw [hw0, zero_dotProduct] at h1 h2
    linarith
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  set v : Fin p → ℝ := (-‖w‖⁻¹) • w with hv
  have hv1 : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_neg, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
  obtain ⟨z, hzC, hz⟩ := hsupp v hv1
  have hfz := hfC z hzC
  rw [hw] at hfy hfz
  rw [hv, smul_dotProduct, smul_eq_mul, dotProduct_sub] at hz
  -- `w ⬝ᵥ (t - y) > δ ‖w‖`
  have hkey : δ * ‖w‖ < w ⬝ᵥ (t - y) := by
    rw [dotProduct_sub]
    have : δ * ‖w‖ ≤ w ⬝ᵥ t - w ⬝ᵥ z := by
      have h2 : δ ≤ -‖w‖⁻¹ * (w ⬝ᵥ z - w ⬝ᵥ t) := hz
      rw [neg_mul, ← mul_neg, neg_sub] at h2
      rwa [le_inv_mul_iff₀ hwn, mul_comm] at h2
    linarith
  have hbd := (le_abs_self _).trans (abs_dotProduct_le_mul_norm w (t - y))
  have hty : ‖t - y‖ < δ / p := by
    rw [← dist_eq_norm, dist_comm]; exact hy
  have : (p : ℝ) * (‖w‖ * ‖t - y‖) < δ * ‖w‖ := by
    calc (p : ℝ) * (‖w‖ * ‖t - y‖) < p * (‖w‖ * (δ / p)) := by gcongr
      _ = δ * ‖w‖ := by field_simp
  linarith

/-- **The interior condition is the margin condition.** `t` lies in the interior of the closed
convex hull of the support of `ν` if and only if there is `δ > 0` with
`ν{y | δ ≤ vᵀ(y - t)} ≥ δ` for every direction `v` of norm one. -/
theorem mem_interior_closedConvexHull_iff_margin :
    t ∈ interior (closedConvexHull ℝ ν.support) ↔
      ∃ δ, 0 < δ ∧ ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {y | δ ≤ v ⬝ᵥ (y - t)} := by
  refine ⟨fun ht => exists_margin_of_measure_pos fun v hv =>
    measure_pos_of_mem_interior_closedConvexHull ht ?_, fun ⟨δ, hδ, h⟩ =>
      mem_interior_closedConvexHull_of_margin hδ h⟩
  rintro rfl; simp at hv

/-- **The interior condition is positive mass beyond the target in every direction.** -/
theorem mem_interior_closedConvexHull_iff_measure_pos :
    t ∈ interior (closedConvexHull ℝ ν.support) ↔
      ∀ v : Fin p → ℝ, v ≠ 0 → 0 < ν {y | 0 < v ⬝ᵥ (y - t)} := by
  refine ⟨fun ht v hv => measure_pos_of_mem_interior_closedConvexHull ht hv, fun h => ?_⟩
  obtain ⟨δ, hδ, hm⟩ := exists_margin_of_measure_pos (ν := ν) (t := t) fun v hv => h v (by
    rintro rfl; simp at hv)
  exact mem_interior_closedConvexHull_of_margin hδ hm

/-- **In the lower dimensional case the margin condition fails.** If the support of `ν` lies in a
proper affine subspace of `ℝ^p`, no `δ > 0` satisfies the margin condition at any target: the
margin would put the target in the interior of the closed convex hull of the support, which is
contained in the affine span of the support and so has empty interior. -/
theorem not_margin_of_affineSpan_ne_top (hspan : affineSpan ℝ ν.support ≠ ⊤) :
    ¬ ∃ δ, 0 < δ ∧ ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {y | δ ≤ v ⬝ᵥ (y - t)} := by
  rintro ⟨δ, hδ, h⟩
  have ht := mem_interior_closedConvexHull_of_margin hδ h
  have hcv : Convex ℝ (closedConvexHull ℝ ν.support) := convex_closedConvexHull
  have htop := (Convex.interior_nonempty_iff_affineSpan_eq_top hcv).1 ⟨t, ht⟩
  have hsub : closedConvexHull ℝ ν.support ⊆ affineSpan ℝ ν.support :=
    closedConvexHull_min (subset_affineSpan ℝ _) (AffineSubspace.convex _)
      (AffineSubspace.isClosed_of_finiteDimensional _)
  refine hspan (eq_top_iff.2 ?_)
  rw [← htop]
  exact affineSpan_le_of_subset_coe hsub

omit [IsProbabilityMeasure ν] in
/-- **The dual parameter is not unique in the lower dimensional case.** If a direction `v` is
orthogonal to every centered sample feature, the dual objective is invariant under adding `v`
to the parameter, so a minimizer, when it exists, is not unique (the weights are). -/
theorem logPartition_add_of_dotProduct_eq_zero {n : ℕ} {Δ : Fin n → Fin p → ℝ} {v : Fin p → ℝ}
    (hv : ∀ i, v ⬝ᵥ Δ i = 0) (β : Fin p → ℝ) : logPartition Δ (β + v) = logPartition Δ β := by
  simp only [logPartition, partitionFunction, add_dotProduct, hv, add_zero]

end Convex

section Records

variable {𝒟 : Type*} [MeasurableSpace 𝒟] {p : ℕ}

/-- **The margin condition for a feature map of records from the interior condition.** If `f` is
a measurable feature map and `t` lies in the interior of the closed convex hull of the support
of the law of `f` under the probability measure `ν`, then for some `δ > 0` and every `v` of norm
one, `ν{z | δ ≤ vᵀ(f(z) - t)} ≥ δ`. -/
theorem exists_margin_of_mem_interior_map {ν : Measure 𝒟} [IsProbabilityMeasure ν]
    {f : 𝒟 → Fin p → ℝ} (hf : Measurable f) {t : Fin p → ℝ}
    (ht : t ∈ interior (closedConvexHull ℝ (ν.map f).support)) :
    ∃ δ, 0 < δ ∧ ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (f z - t)} := by
  obtain ⟨δ, hδ, h⟩ := mem_interior_closedConvexHull_iff_margin.1 ht
  refine ⟨δ, hδ, fun v hv => ?_⟩
  have hs : MeasurableSet {y : Fin p → ℝ | δ ≤ v ⬝ᵥ (y - t)} :=
    measurableSet_le measurable_const (by fun_prop)
  have := h v hv
  rwa [map_measureReal_apply hf hs] at this

/-- The converse: the margin condition for records puts the target in the interior of the closed
convex hull of the support of the feature law. -/
theorem mem_interior_map_of_margin {ν : Measure 𝒟} [IsProbabilityMeasure ν]
    {f : 𝒟 → Fin p → ℝ} (hf : Measurable f) {t : Fin p → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (f z - t)}) :
    t ∈ interior (closedConvexHull ℝ (ν.map f).support) := by
  refine mem_interior_closedConvexHull_of_margin hδ fun v hv => ?_
  have hs : MeasurableSet {y : Fin p → ℝ | δ ≤ v ⬝ᵥ (y - t)} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [map_measureReal_apply hf hs]; exact h v hv

end Records

/-! ### The consistency theorems under the interior condition -/

section Consistency

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {p : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒳 × Bool × ℝ} {Ω' ι : Type*} [MeasurableSpace Ω']

/-- **Consistency of the weighted arm mean under the interior condition.** The hypotheses of
`sampleBalancedArmMean_isConsistent` with the margin condition replaced by the interior
condition: the reported moments `t` lie in the interior of the closed convex hull of the support
of the law of the features `φ(X)` of a record. Then the weighted arm mean with the entropy
balancing weights at `t` is consistent for `a₀ + bᵀt`. -/
theorem sampleBalancedArmMean_isConsistent_of_interior (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    (hint : t ∈ interior (closedConvexHull ℝ ((P.map (O 0)).map fun z => φ z.1).support))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0))) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a}) {mu : Bool → 𝒳 → ℝ} (hmu : ∀ s, Measurable (mu s))
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (sampleBalancedArmMean φ t O a) (a0 + b ⬝ᵥ t) P := by
  obtain ⟨δ, hδ, hm⟩ := exists_margin_of_mem_interior_map (hφ.comp measurable_fst) hint
  exact sampleBalancedArmMean_isConsistent hO hOm hφ hB hδ hm hind a hq hmu hres2 hreg hvar haff

/-- **The limit is the target arm mean, under the interior condition.** The hypotheses of
`sampleBalancedArmMean_isConsistent_armMean` with the interior condition in place of the margin
condition. -/
theorem sampleBalancedArmMean_isConsistent_armMean_of_interior (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    (hint : t ∈ interior (closedConvexHull ℝ ((P.map (O 0)).map fun z => φ z.1).support))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0)))
    (a : Bool) (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a}) {mu : Bool → 𝒳 → ℝ}
    (hmu : ∀ s, Measurable (mu s))
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + b ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta : ι} (hQY : Integrable (Q.Y ta) Q.μ)
    (hQm : Q.IsCondMean ta (mu a)) :
    IsConsistent (sampleBalancedArmMean φ t O a) (Q.armMean ta) P := by
  obtain ⟨δ, hδ, hm⟩ := exists_margin_of_mem_interior_map (hφ.comp measurable_fst) hint
  exact sampleBalancedArmMean_isConsistent_armMean hO hOm hφ hB hδ hm hind a hq hmu hres2 hreg
    hvar haff hQX ht hQY hQm

/-- **Consistency of the unanchored weighted comparison under the interior condition.** The
hypotheses of `unanchoredBalancedEstimate_isConsistent` with the interior condition in place of
the margin condition. -/
theorem unanchoredBalancedEstimate_isConsistent_of_interior (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    (hint : t ∈ interior (closedConvexHull ℝ ((P.map (O 0)).map fun z => φ z.1).support))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0)))
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = true}) {mu : Bool → 𝒳 → ℝ}
    (hmu : ∀ s, Measurable (mu s))
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, mu true x = a0 + b ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta tb : ι} (hQY : Integrable (Q.Y ta) Q.μ)
    (hQm : Q.IsCondMean ta (mu true)) {mB : ℕ → Ω → ℝ}
    (hmB : IsConsistent mB (Q.armMean tb) P) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean ta)) (hgb : ContinuousAt g (Q.armMean tb)) :
    IsConsistent (unanchoredBalancedEstimate g φ t O mB) (Q.marginalEffect g ta tb) P := by
  obtain ⟨δ, hδ, hm⟩ := exists_margin_of_mem_interior_map (hφ.comp measurable_fst) hint
  exact unanchoredBalancedEstimate_isConsistent hO hOm hφ hB hδ hm hind hq hmu hres2 hreg hvar
    haff hQX ht hQY hQm hmB hga hgb

/-- **Consistency of the anchored weighted comparison under the interior condition.** The
hypotheses of `anchoredBalancedEstimate_isConsistent` with the interior condition in place of
the margin condition. -/
theorem anchoredBalancedEstimate_isConsistent_of_interior (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    (hint : t ∈ interior (closedConvexHull ℝ ((P.map (O 0)).map fun z => φ z.1).support))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0)))
    (hqA : 0 < (P.map (O 0)).real {z | z.2.1 = true})
    (hqC : 0 < (P.map (O 0)).real {z | z.2.1 = false}) {mu : Bool → 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0A a0C : ℝ} {bA bC : Fin p → ℝ} (haffA : ∀ x, mu true x = a0A + bA ⬝ᵥ φ x)
    (haffC : ∀ x, mu false x = a0C + bC ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta tb tc : ι} (hQYa : Integrable (Q.Y ta) Q.μ)
    (hQYc : Integrable (Q.Y tc) Q.μ) (hQma : Q.IsCondMean ta (mu true))
    (hQmc : Q.IsCondMean tc (mu false)) {g : ℝ → ℝ} {dBC : ℕ → Ω → ℝ}
    (hBC : IsConsistent dBC (Q.marginalEffect g tb tc) P)
    (hga : ContinuousAt g (Q.armMean ta)) (hgc : ContinuousAt g (Q.armMean tc)) :
    IsConsistent (anchoredBalancedEstimate g φ t O dBC) (Q.marginalEffect g ta tb) P := by
  obtain ⟨δ, hδ, hm⟩ := exists_margin_of_mem_interior_map (hφ.comp measurable_fst) hint
  exact anchoredBalancedEstimate_isConsistent hO hOm hφ hB hδ hm hind hqA hqC hres2 hreg hvar
    haffA haffC hQX ht hQYa hQYc hQma hQmc hBC hga hgc

/-- **Consistency of the anchored weighted comparison on the identity scale under the interior
condition.** The hypotheses of `anchoredBalancedEstimate_isConsistent_identity` with the interior
condition in place of the margin condition. -/
theorem anchoredBalancedEstimate_isConsistent_identity_of_interior (hO : IsIIDSample O P)
    (hOm : ∀ i, Measurable (O i)) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    (hint : t ∈ interior (closedConvexHull ℝ ((P.map (O 0)).map fun z => φ z.1).support))
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0)))
    (hqA : 0 < (P.map (O 0)).real {z | z.2.1 = true})
    (hqC : 0 < (P.map (O 0)).real {z | z.2.1 = false}) {mu : Bool → 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0A a0C : ℝ} {bA bC : Fin p → ℝ} (haffA : ∀ x, mu true x = a0A + bA ⬝ᵥ φ x)
    (haffC : ∀ x, mu false x = a0C + bC ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta tb tc : ι} (hQYa : Integrable (Q.Y ta) Q.μ)
    (hQYc : Integrable (Q.Y tc) Q.μ)
    (hrel : (fun ω => mu false (Q.X ω) - mu true (Q.X ω)) =ᵐ[Q.μ]
      Q.μ[fun ω => Q.Y tc ω - Q.Y ta ω | MeasurableSpace.comap Q.X inferInstance])
    {dBC : ℕ → Ω → ℝ} (hBC : IsConsistent dBC (Q.marginalEffect id tb tc) P) :
    IsConsistent (anchoredBalancedEstimate id φ t O dBC) (Q.marginalEffect id ta tb) P := by
  obtain ⟨δ, hδ, hm⟩ := exists_margin_of_mem_interior_map (hφ.comp measurable_fst) hint
  exact anchoredBalancedEstimate_isConsistent_identity hO hOm hφ hB hδ hm hind hqA hqC hres2
    hreg hvar haffA haffC hQX ht hQYa hQYc hrel hBC

end Consistency

section Trial

variable {Ω 𝒳 Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace Ω₁] {p : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency of the weighted arm mean for the individual data of a randomized trial, under
the interior condition.** The hypotheses of `sampleBalancedArmMean_isConsistent_trial` with the
margin condition replaced by: `t` lies in the interior of the closed convex hull of the support
of the law of the features `φ(X)` under the covariate law of the trial. -/
theorem sampleBalancedArmMean_isConsistent_trial_of_interior {T : Trial Ω₁ 𝒳 Bool}
    (hX : Measurable T.X) (hA : Measurable T.A) (hYo : Measurable T.obsOutcome)
    (hrand : IndepFun T.X T.A T.μ) (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = T.ipdLaw) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (a : Bool) (hq : 0 < T.μ.real (T.A ⁻¹' {a}))
    {mu : Bool → 𝒳 → ℝ} (hmu : ∀ s, Measurable (mu s))
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) T.ipdLaw)
    (hreg : T.ipdLaw[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[T.ipdLaw]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : T.ipdLaw[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, mu a x = a0 + b ⬝ᵥ φ x) :
    IsConsistent (sampleBalancedArmMean φ t O a) (a0 + b ⬝ᵥ t) P := by
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have : IsProbabilityMeasure (T.μ.map fun ω => (T.X ω, T.A ω, T.obsOutcome ω)) := by
    change IsProbabilityMeasure T.ipdLaw
    rw [← hlaw]; infer_instance
  have : IsProbabilityMeasure T.μ := Measure.isProbabilityMeasure_of_map hf.aemeasurable
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hX
  obtain ⟨δ, hδ, hm⟩ := exists_margin_of_mem_interior_map hφ hint
  exact sampleBalancedArmMean_isConsistent_trial hX hA hYo hrand hO hOm hlaw hφ hB hδ hm a hq
    hmu hres2 hreg hvar haff

end Trial

end PopulationAdjustment

end CausalInference
