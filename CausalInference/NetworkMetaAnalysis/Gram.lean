/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.Incidence
public import Mathlib.Algebra.Order.Star.Real

/-!
# Network meta-analysis: the weighted Gram matrix as a weighted Laplacian

For a design matrix `X` and a positive definite weight matrix `W`, the **weighted Gram matrix**
`Xᵀ W X` has the kernel of `X` (`ker_transpose_mul_mul`), so it is invertible, and then
positive definite, exactly when `X` has full column rank (`isUnit_transpose_mul_mul_iff`,
`posDef_transpose_mul_mul_iff`).

For the incidence matrix `B` of a network and positive comparison weights `w_e` (inverse
variances), `L_w = Bᵀ diag(w) B` is the **weighted Laplacian** of the network
(`weightedLaplacian`): its quadratic form is `∑_e w_e (θ_{head e} - θ_{tail e})²`
(`dotProduct_weightedLaplacian_mulVec`), its rank is `T - q` (`rank_weightedLaplacian_add_card`),
and its restriction to the basic parameters of a reference treatment, the reduced Gram matrix
`Xᵀ diag(w) X` of the reduced design (`reducedGram`), is positive definite exactly when the
network is connected (`posDef_reducedGram_iff`). For a simple network (no comparison of a
treatment with itself and at most one comparison per pair) with unit weights, `L_w` is the
Laplacian `SimpleGraph.lapMatrix` of the comparison graph (`weightedLaplacian_one_eq_lapMatrix`).

## Main definitions

* `weightedLaplacian`, `reducedGram`.

## Main results

* `ker_transpose_mul_mul`, `isUnit_transpose_mul_mul_iff`, `posDef_transpose_mul_mul_iff`.
* `dotProduct_weightedLaplacian_mulVec`, `rank_weightedLaplacian_add_card`.
* `reducedGram_eq_submatrix`, `posDef_reducedGram_iff`, `isUnit_reducedGram_iff`.
* `weightedLaplacian_one_eq_lapMatrix`.

## References

* G. Rücker, *Network meta-analysis, electrical networks and graph theory*, Research Synthesis
  Methods 3 (2012).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix

/-! ### The weighted Gram matrix of a design -/

section Gram

variable {n p : Type*} [Fintype n] [Fintype p]

/-- Moving a matrix across a dot product: `(X h) ⬝ u = h ⬝ (Xᵀ u)`. -/
theorem mulVec_dotProduct_eq (X : Matrix n p ℝ) (h : p → ℝ) (u : n → ℝ) :
    (X *ᵥ h) ⬝ᵥ u = h ⬝ᵥ (Xᵀ *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

/-- The quadratic form of the weighted Gram matrix: `hᵀ (Xᵀ W X) h = (X h)ᵀ W (X h)`. -/
theorem dotProduct_transpose_mul_mul_mulVec (X : Matrix n p ℝ) (W : Matrix n n ℝ) (h : p → ℝ) :
    h ⬝ᵥ ((Xᵀ * W * X) *ᵥ h) = (X *ᵥ h) ⬝ᵥ (W *ᵥ (X *ᵥ h)) := by
  rw [mulVec_dotProduct_eq, ← mulVec_mulVec, ← mulVec_mulVec]

/-- **The weighted Gram matrix has the kernel of the design**: for `W` positive definite,
`(Xᵀ W X) h = 0` if and only if `X h = 0`. -/
theorem ker_transpose_mul_mul {X : Matrix n p ℝ} {W : Matrix n n ℝ} (hW : W.PosDef) :
    LinearMap.ker (Xᵀ * W * X).mulVecLin = LinearMap.ker X.mulVecLin := by
  ext h
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hh
    by_contra hne
    have hpos := hW.dotProduct_mulVec_pos hne
    rw [star_trivial, ← dotProduct_transpose_mul_mul_mulVec, hh, dotProduct_zero] at hpos
    exact lt_irrefl _ hpos
  · intro hh
    rw [← mulVec_mulVec, hh, mulVec_zero]

theorem injective_transpose_mul_mul_iff {X : Matrix n p ℝ} {W : Matrix n n ℝ} (hW : W.PosDef) :
    Function.Injective (Xᵀ * W * X).mulVec ↔ Function.Injective X.mulVec := by
  have h1 : Function.Injective (Xᵀ * W * X).mulVec ↔
      LinearMap.ker (Xᵀ * W * X).mulVecLin = ⊥ := by rw [LinearMap.ker_eq_bot]; exact Iff.rfl
  have h2 : Function.Injective X.mulVec ↔ LinearMap.ker X.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]; exact Iff.rfl
  rw [h1, h2, ker_transpose_mul_mul hW]

/-- **Invertibility of the weighted Gram matrix**: for `W` positive definite, `Xᵀ W X` is
invertible if and only if `X` has full column rank. -/
theorem isUnit_transpose_mul_mul_iff [DecidableEq p] {X : Matrix n p ℝ} {W : Matrix n n ℝ}
    (hW : W.PosDef) : IsUnit (Xᵀ * W * X) ↔ Function.Injective X.mulVec := by
  rw [← mulVec_injective_iff_isUnit, injective_transpose_mul_mul_iff hW]

/-- **Positive definiteness of the weighted Gram matrix**: for `W` positive definite, `Xᵀ W X`
is positive definite if and only if `X` has full column rank. -/
theorem posDef_transpose_mul_mul_iff {X : Matrix n p ℝ} {W : Matrix n n ℝ} (hW : W.PosDef) :
    (Xᵀ * W * X).PosDef ↔ Function.Injective X.mulVec := by
  classical
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← injective_transpose_mul_mul_iff hW, mulVec_injective_iff_isUnit]
    exact h.isUnit
  · simpa [conjTranspose_eq_transpose_of_trivial] using hW.conjTranspose_mul_mul_same h

/-- The weighted Gram matrix has the rank of the design, for `W` positive definite. -/
theorem rank_transpose_mul_mul {X : Matrix n p ℝ} {W : Matrix n n ℝ} (hW : W.PosDef) :
    (Xᵀ * W * X).rank = X.rank := by
  have h1 := (Xᵀ * W * X).mulVecLin.finrank_range_add_finrank_ker
  have h2 := X.mulVecLin.finrank_range_add_finrank_ker
  rw [ker_transpose_mul_mul hW] at h1
  unfold Matrix.rank
  omega

end Gram

/-! ### The weighted Laplacian of a network -/

section Laplacian

variable {E K : Type*} [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

/-- The **weighted Laplacian** `L_w = Bᵀ diag(w) B` of a network of comparisons with weights
`w_e`, for the incidence matrix `B`. -/
def weightedLaplacian (tail head : E → K) (w : E → ℝ) : Matrix K K ℝ :=
  (incidenceMatrix tail head)ᵀ * diagonal w * incidenceMatrix tail head

/-- **The quadratic form of the weighted Laplacian**:
`θᵀ L_w θ = ∑_e w_e (θ_{head e} - θ_{tail e})²`. -/
theorem dotProduct_weightedLaplacian_mulVec (tail head : E → K) (w : E → ℝ) (θ : K → ℝ) :
    θ ⬝ᵥ (weightedLaplacian tail head w *ᵥ θ) = ∑ e, w e * (θ (head e) - θ (tail e)) ^ 2 := by
  rw [weightedLaplacian, dotProduct_transpose_mul_mul_mulVec]
  simp only [dotProduct, mulVec_diagonal, incidenceMatrix_mulVec]
  exact Finset.sum_congr rfl fun e _ => by ring

omit [Fintype K] in
/-- The weighted Laplacian is symmetric. -/
theorem transpose_weightedLaplacian (tail head : E → K) (w : E → ℝ) :
    (weightedLaplacian tail head w)ᵀ = weightedLaplacian tail head w := by
  simp [weightedLaplacian, transpose_mul, Matrix.mul_assoc]

/-- **Rank of the weighted Laplacian**: for positive weights, `rank L_w + q = T`, with `q` the
number of connected components. -/
theorem rank_weightedLaplacian_add_card (tail head : E → K) {w : E → ℝ} (hw : ∀ e, 0 < w e) :
    (weightedLaplacian tail head w).rank +
        Nat.card (comparisonGraph tail head).ConnectedComponent = Fintype.card K := by
  rw [weightedLaplacian, rank_transpose_mul_mul (posDef_diagonal_iff.2 hw)]
  exact rank_incidenceMatrix_add_card tail head

/-- The **reduced Gram matrix** `Xᵀ diag(w) X` of the reduced design with reference treatment
`r`. -/
def reducedGram (tail head : E → K) (r : K) (w : E → ℝ) : Matrix {k // k ≠ r} {k // k ≠ r} ℝ :=
  (reducedDesign tail head r)ᵀ * diagonal w * reducedDesign tail head r

omit [Fintype K] in
/-- The reduced Gram matrix is the weighted Laplacian with the row and the column of the
reference treatment deleted. -/
theorem reducedGram_eq_submatrix (tail head : E → K) (r : K) (w : E → ℝ) :
    reducedGram tail head r w =
      (weightedLaplacian tail head w).submatrix Subtype.val Subtype.val := by
  ext a b
  simp [reducedGram, weightedLaplacian, reducedDesign, Matrix.mul_apply]

omit [Fintype K] in
/-- **The reduced Gram matrix is positive definite exactly for a connected network**: for
positive weights and a reference treatment `r`, `Xᵀ diag(w) X` is positive definite if and only
if the comparison graph is connected. -/
theorem posDef_reducedGram_iff [Finite K] (tail head : E → K) (r : K) {w : E → ℝ}
    (hw : ∀ e, 0 < w e) :
    (reducedGram tail head r w).PosDef ↔ (comparisonGraph tail head).Connected := by
  have := Fintype.ofFinite K
  rw [reducedGram, posDef_transpose_mul_mul_iff (posDef_diagonal_iff.2 hw),
    reducedDesign_injective_iff]

/-- **The reduced Gram matrix is invertible exactly for a connected network**, for positive
weights. -/
theorem isUnit_reducedGram_iff (tail head : E → K) (r : K) {w : E → ℝ} (hw : ∀ e, 0 < w e) :
    IsUnit (reducedGram tail head r w) ↔ (comparisonGraph tail head).Connected := by
  rw [reducedGram, isUnit_transpose_mul_mul_iff (posDef_diagonal_iff.2 hw),
    reducedDesign_injective_iff]

/-- **The unweighted Laplacian of a simple network** is the Laplacian of its comparison graph:
if no comparison compares a treatment with itself and no two comparisons join the same pair of
treatments (in either orientation), then `Bᵀ B = D - A` for the degree matrix `D` and the
adjacency matrix `A` of the comparison graph. -/
theorem weightedLaplacian_one_eq_lapMatrix (tail head : E → K) (hloop : ∀ e, tail e ≠ head e)
    (hinj : Function.Injective fun e => s(tail e, head e))
    [DecidableRel (comparisonGraph tail head).Adj] :
    weightedLaplacian tail head 1 = (comparisonGraph tail head).lapMatrix ℝ := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => funext fun a => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, SimpleGraph.lapMatrix_mulVec_apply']
  have hL : (weightedLaplacian tail head 1 *ᵥ x) a =
      ∑ e ∈ Finset.univ.filter (fun e => head e = a), (x a - x (tail e)) +
        ∑ e ∈ Finset.univ.filter (fun e => tail e = a), (x a - x (head e)) := by
    rw [weightedLaplacian, show diagonal (1 : E → ℝ) = 1 from diagonal_one, Matrix.mul_one,
      ← mulVec_mulVec, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    simp only [mulVec, dotProduct, transpose_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hm := incidenceMatrix_mulVec tail head x e
    simp only [mulVec, dotProduct] at hm
    rw [hm]
    by_cases hh : head e = a
    · have ht : tail e ≠ a := fun h => hloop e (h.trans hh.symm)
      simp [incidenceMatrix, hh, ht, Ne.symm ht]
    · by_cases ht : tail e = a
      · simp [incidenceMatrix, hh, ht, Ne.symm hh]
      · simp [incidenceMatrix, Ne.symm hh, Ne.symm ht, hh, ht]
  have hpair : ∀ e e', s(tail e, head e) = s(tail e', head e') → e = e' := fun e e' h => hinj h
  rw [hL, ← Finset.sum_image (s := Finset.univ.filter (fun e => head e = a)) (g := tail)
      (f := fun u => x a - x u) ?_,
    ← Finset.sum_image (s := Finset.univ.filter (fun e => tail e = a)) (g := head)
      (f := fun u => x a - x u) ?_, ← Finset.sum_union ?_]
  · congr 1
    ext u
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset, comparisonGraph_adj]
    constructor
    · rintro (⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩)
      · exact ⟨fun h => hloop e h.symm, Or.inr ⟨e, rfl, rfl⟩⟩
      · exact ⟨hloop e, Or.inl ⟨e, rfl, rfl⟩⟩
    · rintro ⟨-, ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩⟩
      · exact Or.inr ⟨e, rfl, rfl⟩
      · exact Or.inl ⟨e, rfl, rfl⟩
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro u ⟨e, he, rfl⟩ ⟨e', he', hu⟩
    have : e = e' := hpair e e' (by rw [he, ← he', hu, Sym2.eq_swap])
    subst this
    exact hloop e (he'.trans he.symm)
  · intro e he e' he' h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he he'
    exact hpair e e' (by rw [h, he, he'])
  · intro e he e' he' h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he he'
    exact hpair e e' (by rw [h, he, he'])

end Laplacian

end NetworkMetaAnalysis

end CausalInference
