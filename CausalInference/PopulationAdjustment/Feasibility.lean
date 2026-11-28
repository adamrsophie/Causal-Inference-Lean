/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.EntropyExistence
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.Combination

/-!
# Population adjustment: feasibility of moment balance

The features `zᵢ = φ(xᵢ)` of a sample can be reweighted to the target means `t` exactly when `t`
is a convex combination of them:

* nonnegative weights summing to one with weighted mean `t` exist exactly when `t` lies in the
  convex hull of the `zᵢ` (`balancingSet_nonempty_iff`);
* strictly positive such weights exist exactly when `t` lies in the relative interior (Mathlib's
  `intrinsicInterior`) of the convex hull (`exists_pos_mem_balancingSet_iff`), and this is
  exactly when the dual of entropy balancing has a minimizer, that is, when the exponential
  tilting weights with finite parameters balance the sample
  (`exists_isMinOn_logPartition_iff_mem_intrinsicInterior`,
  `exists_tiltWeight_mem_balancingSet_iff`).

A target on the relative boundary of the hull can be balanced only by weights that vanish on some
units, which no finite exponential tilt produces; a target outside the hull cannot be balanced at
all. The geometric step is `mem_intrinsicInterior_convexHull_range_iff`: a point lies in the
relative interior of the convex hull of finitely many points exactly when it is a convex
combination of them with strictly positive coefficients.

## Main results

* `mem_convexHull_range_iff`, `mem_intrinsicInterior_convexHull_range_iff`.
* `balancingSet_nonempty_iff`, `exists_pos_mem_balancingSet_iff`,
  `exists_isMinOn_logPartition_iff_mem_intrinsicInterior`,
  `exists_tiltWeight_mem_balancingSet_iff`.
* `not_mem_intrinsicInterior_example`: two units with features `0` and `1` and target `1`: the
  target is in the hull but on its relative boundary, so no strictly positive weights balance.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970.
* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open Finset

/-! ### Convex hulls of finitely many points -/

section ConvexHull

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (v : ι → E)

/-- A point lies in the convex hull of `v₁, …, vₙ` exactly when it is a convex combination
`∑ᵢ qᵢ vᵢ` with `q ≥ 0` and `∑ᵢ qᵢ = 1`. -/
theorem mem_convexHull_range_iff (y : E) :
    y ∈ convexHull ℝ (Set.range v) ↔
      ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ ∑ i, q i • v i = y := by
  classical
  constructor
  · intro h
    rw [convexHull_range_eq_exists_affineCombination] at h
    obtain ⟨s, w, hw0, hw1, rfl⟩ := h
    refine ⟨fun i => if i ∈ s then w i else 0, fun i => ?_, ?_, ?_⟩
    · change 0 ≤ if i ∈ s then w i else 0
      split_ifs with hi
      · exact hw0 i hi
      · exact le_rfl
    · simpa using hw1
    · rw [Finset.affineCombination_eq_linear_combination s v w hw1]
      simp [ite_smul]
  · rintro ⟨q, hq0, hq1, rfl⟩
    exact mem_convexHull_of_exists_fintype q v hq0 hq1 (fun i => ⟨i, rfl⟩) rfl

variable [FiniteDimensional ℝ E]

/-- **The relative interior of the convex hull of finitely many points**: a point lies in the
relative interior of `conv{v₁, …, vₙ}` exactly when it is a convex combination with strictly
positive coefficients. For the forward direction, the segment from the barycenter through the
point is extended a little inside the hull and the extended point is mixed with the barycenter.
For the converse, the point is pushed slightly away from a relative interior point while keeping
nonnegative coefficients, and the open segment lemma of the intrinsic interior applies. -/
theorem mem_intrinsicInterior_convexHull_range_iff (y : E) :
    y ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range v)) ↔
      ∃ q : ι → ℝ, (∀ i, 0 < q i) ∧ ∑ i, q i = 1 ∧ ∑ i, q i • v i = y := by
  set C := convexHull ℝ (Set.range v) with hCdef
  have hconv : Convex ℝ C := convex_convexHull ℝ _
  have hle1 : ∀ q : ι → ℝ, (∀ i, 0 ≤ q i) → ∑ i, q i = 1 → ∀ i, q i ≤ 1 :=
    fun q hq0 hq1 i => hq1 ▸ Finset.single_le_sum (fun j _ => hq0 j) (mem_univ i)
  constructor
  · intro hy
    have hyC : y ∈ C := intrinsicInterior_subset hy
    obtain ⟨q₀, -, hq₀1, -⟩ := (mem_convexHull_range_iff v y).1 hyC
    have : Nonempty ι := nonempty_of_sum_eq_one hq₀1
    set n : ℝ := (Fintype.card ι : ℝ)
    have hn' : (0 : ℝ) < n := by simp only [n]; exact_mod_cast Fintype.card_pos
    set b : E := ∑ i, (1 / n) • v i with hb
    have hbC : b ∈ C := (mem_convexHull_range_iff v b).2
      ⟨fun _ => 1 / n, fun _ => by positivity, by simp [n, hn'.ne'], rfl⟩
    obtain ⟨y', hy'int, hy'eq⟩ := mem_intrinsicInterior.1 hy
    let φ : ℝ → affineSpan ℝ C := fun s => ⟨AffineMap.lineMap b y (1 + s),
      AffineMap.lineMap_mem _ (subset_affineSpan _ _ hbC) (subset_affineSpan _ _ hyC)⟩
    have hφc : Continuous φ := by
      refine Continuous.subtype_mk ?_ _
      simp_rw [AffineMap.lineMap_apply_module]
      fun_prop
    have hφ0 : φ 0 = y' := Subtype.ext (by simp [φ, hy'eq])
    have hnhds : φ ⁻¹' interior ((↑) ⁻¹' C) ∈ nhds (0 : ℝ) :=
      hφc.continuousAt.preimage_mem_nhds (by rw [hφ0]; exact isOpen_interior.mem_nhds hy'int)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnhds
    set s := δ / 2 with hs
    have hs0 : 0 < s := by positivity
    have hsφ : φ s ∈ interior ((↑) ⁻¹' C) :=
      hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs0]; linarith)
    have hzC : AffineMap.lineMap b y (1 + s) ∈ C := by
      have := interior_subset hsφ
      exact this
    obtain ⟨r, hr0, hr1, hrz⟩ := (mem_convexHull_range_iff v _).1 hzC
    refine ⟨fun i => (r i + s / n) / (1 + s), fun i => by have := hr0 i; positivity, ?_, ?_⟩
    · rw [← Finset.sum_div, Finset.sum_add_distrib, hr1]
      simp only [Finset.sum_const, card_univ, nsmul_eq_mul]
      field_simp
      simp only [n]
      ring
    · have hz' : ∑ i, r i • v i = (-s) • b + (1 + s) • y := by
        rw [hrz, AffineMap.lineMap_apply_module]
        congr 1
        ring_nf
      have hexp : ∑ i, ((r i + s / n) / (1 + s)) • v i =
          (1 + s)⁻¹ • (∑ i, r i • v i + s • b) := by
        rw [hb, Finset.smul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul s, ← add_smul, smul_smul]
        congr 1
        field_simp
      rw [hexp, hz', show (-s) • b + (1 + s) • y + s • b = (1 + s) • y by module, smul_smul,
        inv_mul_cancel₀ (by linarith), one_smul]
  · rintro ⟨q, hq0, hq1, rfl⟩
    have : Nonempty ι := nonempty_of_sum_eq_one hq1
    obtain ⟨i₀⟩ := this
    have hne : C.Nonempty := ⟨v i₀, subset_convexHull ℝ _ ⟨_, rfl⟩⟩
    obtain ⟨c, hc⟩ := Set.Nonempty.intrinsicInterior hconv hne
    obtain ⟨r, hr0, hr1, hrc⟩ := (mem_convexHull_range_iff v c).1 (intrinsicInterior_subset hc)
    obtain ⟨k, -, hk⟩ := Finset.exists_min_image univ q ⟨i₀, mem_univ _⟩
    set ε := q k / 2 with hε
    have hε0 : 0 < ε := by have := hq0 k; positivity
    have hε1 : ε < 1 := by have := hle1 q (fun i => (hq0 i).le) hq1 k; linarith
    have hcoef : ∀ i, 0 ≤ (q i - ε * r i) / (1 - ε) := by
      intro i
      have hri := hle1 r hr0 hr1 i
      have hki := hk i (mem_univ _)
      have : ε * r i ≤ ε := by nlinarith [hr0 i]
      exact div_nonneg (by linarith) (by linarith)
    set z := ∑ i, ((q i - ε * r i) / (1 - ε)) • v i with hz
    have hzC : z ∈ C := (mem_convexHull_range_iff v z).2 ⟨_, hcoef, by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hq1, hr1, mul_one,
        div_self (by linarith)], rfl⟩
    have hseg : ∑ i, q i • v i ∈ openSegment ℝ c z := by
      refine ⟨ε, 1 - ε, hε0, by linarith, by ring, ?_⟩
      rw [← hrc, hz, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, smul_smul, ← add_smul]
      congr 1
      field_simp
      ring
    exact hconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hc
      (subset_intrinsicClosure hzC) hseg

end ConvexHull

/-! ### Feasibility of moment balance -/

section Feasibility

variable {ι : Type*} [Fintype ι] {p : ℕ} (z : ι → Fin p → ℝ) (t : Fin p → ℝ)

/-- **Feasibility of moment balance**: some probability vector reweights the features `zᵢ` to
the mean `t` exactly when `t` lies in the convex hull of the `zᵢ`, equivalently when `0` lies in
the convex hull of the centered features `zᵢ - t`. -/
theorem balancingSet_nonempty_iff :
    ((balancingSet fun i => z i - t).Nonempty ↔ t ∈ convexHull ℝ (Set.range z)) ∧
      ((balancingSet fun i => z i - t).Nonempty ↔
        (0 : Fin p → ℝ) ∈ convexHull ℝ (Set.range fun i => z i - t)) := by
  constructor
  · rw [mem_convexHull_range_iff]
    exact ⟨fun ⟨q, hq⟩ => ⟨q, mem_balancingSet_sub_iff.1 hq⟩,
      fun ⟨q, hq⟩ => ⟨q, mem_balancingSet_sub_iff.2 hq⟩⟩
  · rw [mem_convexHull_range_iff]
    refine ⟨fun ⟨q, hq0, hq1, hqb⟩ => ⟨q, hq0, hq1, ?_⟩,
      fun ⟨q, hq0, hq1, hqb⟩ => ⟨q, hq0, hq1, ?_⟩⟩
    · exact momentBalanced_zero_iff.1 hqb
    · exact momentBalanced_zero_iff.2 hqb

/-- **Strictly positive balancing weights exist exactly at a relative interior target**:
`t ∈ relint conv{zᵢ}`, equivalently `0 ∈ relint conv{zᵢ - t}`. -/
theorem exists_pos_mem_balancingSet_iff :
    ((∃ q ∈ balancingSet (fun i => z i - t), ∀ i, 0 < q i) ↔
        t ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range z))) ∧
      ((∃ q ∈ balancingSet (fun i => z i - t), ∀ i, 0 < q i) ↔
        (0 : Fin p → ℝ) ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range fun i => z i - t))) := by
  constructor
  · rw [mem_intrinsicInterior_convexHull_range_iff]
    refine ⟨fun ⟨q, hq, hpos⟩ => ⟨q, hpos, ?_⟩, fun ⟨q, hpos, hq⟩ => ⟨q, ?_, hpos⟩⟩
    · exact (mem_balancingSet_sub_iff.1 hq).2
    · exact mem_balancingSet_sub_iff.2 ⟨fun i => (hpos i).le, hq⟩
  · rw [mem_intrinsicInterior_convexHull_range_iff]
    refine ⟨fun ⟨q, ⟨_, hq1, hqb⟩, hpos⟩ => ⟨q, hpos, hq1, momentBalanced_zero_iff.1 hqb⟩,
      fun ⟨q, hpos, hq1, hqb⟩ => ⟨q, ⟨fun i => (hpos i).le, hq1,
        momentBalanced_zero_iff.2 hqb⟩, hpos⟩⟩

/-- **The dual of entropy balancing has a minimizer exactly at a relative interior target**, for
a nonempty sample. -/
theorem exists_isMinOn_logPartition_iff_mem_intrinsicInterior [Nonempty ι] :
    (∃ β, IsMinOn (logPartition fun i => z i - t) Set.univ β) ↔
      t ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range z)) :=
  exists_isMinOn_logPartition_iff.trans (exists_pos_mem_balancingSet_iff z t).1

/-- **Finite exponential weights exist exactly at a relative interior target**: some tilting
weights `exp(α + βᵀ(zᵢ - t))` with finite `(α, β)` form a balancing probability vector of
minimal negative entropy exactly when `t ∈ relint conv{zᵢ}`. -/
theorem exists_tiltWeight_mem_balancingSet_iff [Nonempty ι] :
    (∃ (α : ℝ) (β : Fin p → ℝ), (fun i => tiltWeight z t α β i) ∈ balancingSet (fun i => z i - t)
      ∧ IsMinOn negEntropy (balancingSet fun i => z i - t) (fun i => tiltWeight z t α β i)) ↔
      t ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range z)) := by
  rw [← (exists_pos_mem_balancingSet_iff z t).1]
  constructor
  · rintro ⟨α, β, hf, -⟩
    exact ⟨_, hf, tiltWeight_pos z t α β⟩
  · intro hpos
    obtain ⟨β, hβ⟩ := exists_isMinOn_logPartition hpos
    obtain ⟨h1, -, h3, -⟩ := entropyWeights_isMinOn ((isMinOn_logPartition_iff β).1 hβ)
    refine ⟨-logPartition (fun i => z i - t) β, β, ?_⟩
    have heq : (fun i => tiltWeight z t (-logPartition (fun i => z i - t) β) β i) =
        entropyWeights (fun i => z i - t) β := by
      funext i
      exact (entropyWeights_eq_tiltWeight z id t β i).symm
    rw [heq]
    exact ⟨h1, h3⟩

/-- **A target on the relative boundary**: with two units of features `0` and `1` and target
`1`, the target lies in the convex hull but not in its relative interior, so moment balance is
feasible but no strictly positive weights (and no finite exponential tilt) balance the
sample. -/
theorem not_mem_intrinsicInterior_example :
    let z : Fin 2 → Fin 1 → ℝ := ![fun _ => 0, fun _ => 1]
    (balancingSet fun i => z i - fun _ => 1).Nonempty ∧
      ¬ ∃ q ∈ balancingSet (fun i => z i - fun _ => 1), ∀ i, 0 < q i := by
  intro z
  refine ⟨⟨![0, 1], ?_⟩, ?_⟩
  · refine mem_balancingSet_sub_iff.2 ⟨fun i => by fin_cases i <;> simp, by simp, ?_⟩
    funext j; simp [z, Fin.sum_univ_two]
  · rintro ⟨q, hq, hpos⟩
    obtain ⟨-, hq1, hqz⟩ := mem_balancingSet_sub_iff.1 hq
    have h := congrFun hqz 0
    simp only [Fin.sum_univ_two, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, z,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h hq1
    have := hpos 0
    linarith

end Feasibility

end PopulationAdjustment

end CausalInference
