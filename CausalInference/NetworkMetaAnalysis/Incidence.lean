/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Network meta-analysis: the signed incidence matrix of a network of comparisons

A network of treatment comparisons is a finite family `E` of comparisons, each an ordered pair
of treatments: comparison `e` compares `head e` with `tail e`, and its contrast is the effect of
`head e` relative to `tail e`, `θ_{head e} - θ_{tail e}` for a vector `θ` of treatment levels.
Parallel comparisons (several studies of the same pair, or several contrasts of one multi-arm
study) are distinct elements of `E`, so the network is a multigraph on the treatments.

The **signed incidence matrix** (contrast design matrix) `B` has the row `+1` at `head e`, `-1`
at `tail e` (`incidenceMatrix`), so `(B θ)_e = θ_{head e} - θ_{tail e}`. Its kernel is the set of
level vectors constant on each connected component of the comparison graph
(`incidenceMatrix_mulVec_eq_zero_iff_reachable`), hence `rank B + q = T` with `q` the number of
connected components and `T` the number of treatments (`rank_incidenceMatrix_add_card`), and
`rank B + 1 = T` exactly when the network is connected.

With a reference treatment `r` the **basic parameters** are the contrasts `d_k = θ_k - θ_r`,
`k ≠ r`; the padded vector `padReference r d` puts `0` at `r`. The **reduced design**
`reducedDesign` (the columns `k ≠ r` of `B`) has full column rank exactly when the network is
connected (`reducedDesign_injective_iff`).

## Main definitions

* `incidenceMatrix`, `comparisonGraph`, `padReference`, `reducedDesign`.

## Main results

* `incidenceMatrix_mulVec`, `incidenceMatrix_mulVec_eq_zero_iff`,
  `incidenceMatrix_mulVec_eq_zero_iff_reachable`.
* `finrank_ker_incidenceMatrix`, `rank_incidenceMatrix_add_card`,
  `rank_incidenceMatrix_add_one_iff`.
* `reducedDesign_mulVec`, `reducedDesign_injective_iff`, `rank_reducedDesign_iff`,
  `rank_reducedDesign`.

## References

* G. Rücker, *Network meta-analysis, electrical networks and graph theory*, Research Synthesis
  Methods 3 (2012).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix

section Incidence

variable {E K : Type*} [Fintype K] [DecidableEq K]

/-- The **signed incidence matrix** of a network of comparisons: comparison `e` compares
`head e` with `tail e`, and its row has `+1` in the column `head e`, `-1` in the column `tail e`,
and `0` elsewhere (a comparison of a treatment with itself gives a zero row). -/
def incidenceMatrix (tail head : E → K) : Matrix E K ℝ :=
  Matrix.of fun e k => (if k = head e then 1 else 0) - (if k = tail e then 1 else 0)

/-- The **comparison graph**: two distinct treatments are adjacent when some comparison joins
them, in either orientation. It has the connected components of the multigraph of
comparisons. -/
def comparisonGraph (tail head : E → K) : SimpleGraph K :=
  SimpleGraph.fromRel fun a b => ∃ e, tail e = a ∧ head e = b

omit [Fintype K] [DecidableEq K] in
theorem comparisonGraph_adj {tail head : E → K} {a b : K} :
    (comparisonGraph tail head).Adj a b ↔
      a ≠ b ∧ ((∃ e, tail e = a ∧ head e = b) ∨ ∃ e, tail e = b ∧ head e = a) :=
  SimpleGraph.fromRel_adj _ _ _

omit [Fintype K] [DecidableEq K] in
/-- The two ends of a comparison of distinct treatments are adjacent. -/
theorem comparisonGraph_adj_of_ne {tail head : E → K} (e : E) (h : tail e ≠ head e) :
    (comparisonGraph tail head).Adj (tail e) (head e) :=
  comparisonGraph_adj.2 ⟨h, Or.inl ⟨e, rfl, rfl⟩⟩

/-- The incidence matrix takes contrasts: `(B θ)_e = θ_{head e} - θ_{tail e}`. -/
theorem incidenceMatrix_mulVec (tail head : E → K) (θ : K → ℝ) (e : E) :
    (incidenceMatrix tail head *ᵥ θ) e = θ (head e) - θ (tail e) := by
  simp [incidenceMatrix, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- `B θ = 0` exactly when `θ` takes equal values at the two ends of every comparison. -/
theorem incidenceMatrix_mulVec_eq_zero_iff (tail head : E → K) (θ : K → ℝ) :
    incidenceMatrix tail head *ᵥ θ = 0 ↔
      ∀ a b, (comparisonGraph tail head).Adj a b → θ a = θ b := by
  constructor
  · intro h a b hab
    obtain ⟨-, ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩⟩ := comparisonGraph_adj.1 hab
    · have := congrFun h e
      rw [incidenceMatrix_mulVec, Pi.zero_apply] at this
      linarith
    · have := congrFun h e
      rw [incidenceMatrix_mulVec, Pi.zero_apply] at this
      linarith
  · intro h
    funext e
    rw [incidenceMatrix_mulVec, Pi.zero_apply, sub_eq_zero]
    by_cases hte : tail e = head e
    · rw [hte]
    · exact (h _ _ (comparisonGraph_adj_of_ne e hte)).symm

/-- **The kernel of the incidence matrix** is the set of level vectors constant on the connected
components of the comparison graph. -/
theorem incidenceMatrix_mulVec_eq_zero_iff_reachable (tail head : E → K) (θ : K → ℝ) :
    incidenceMatrix tail head *ᵥ θ = 0 ↔
      ∀ a b, (comparisonGraph tail head).Reachable a b → θ a = θ b := by
  classical
  rw [incidenceMatrix_mulVec_eq_zero_iff,
    ← SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj,
    SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable]

/-- The kernel of the incidence matrix has dimension the number of connected components of the
comparison graph: it is the kernel of the Laplacian of that graph, whose dimension Mathlib
computes. -/
theorem finrank_ker_incidenceMatrix (tail head : E → K) :
    Module.finrank ℝ (LinearMap.ker (incidenceMatrix tail head).mulVecLin) =
      Nat.card (comparisonGraph tail head).ConnectedComponent := by
  classical
  have hker : LinearMap.ker (incidenceMatrix tail head).mulVecLin =
      LinearMap.ker (Matrix.toLin' ((comparisonGraph tail head).lapMatrix ℝ)) := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.toLin'_apply]
    rw [incidenceMatrix_mulVec_eq_zero_iff, SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj]
  rw [hker, ← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix,
    Nat.card_eq_fintype_card]

/-- **The rank of the incidence matrix**: `rank B + q = T`, where `q` is the number of connected
components of the comparison graph and `T` the number of treatments (stated additively, without
truncated subtraction). -/
theorem rank_incidenceMatrix_add_card (tail head : E → K) :
    (incidenceMatrix tail head).rank + Nat.card (comparisonGraph tail head).ConnectedComponent =
      Fintype.card K := by
  have h := (incidenceMatrix tail head).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, finrank_ker_incidenceMatrix] at h
  exact h

/-- **Rank `T - 1` exactly for a connected network**: `rank B + 1 = T` if and only if the
comparison graph is connected. -/
theorem rank_incidenceMatrix_add_one_iff (tail head : E → K) :
    (incidenceMatrix tail head).rank + 1 = Fintype.card K ↔
      (comparisonGraph tail head).Connected := by
  rw [← SimpleGraph.card_connectedComponent_eq_one_iff]
  have := rank_incidenceMatrix_add_card tail head
  omega

end Incidence

/-! ### Full column rank -/

section Rank

variable {n p : Type*} [Fintype p]

/-- **Full column rank**: `rank X = p` if and only if `v ↦ X v` is injective. -/
theorem rank_eq_card_iff_injective_mulVec (X : Matrix n p ℝ) :
    X.rank = Fintype.card p ↔ Function.Injective X.mulVec := by
  have h := X.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at h
  have hinj : Function.Injective X.mulVec ↔ LinearMap.ker X.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]; exact Iff.rfl
  rw [hinj, ← Submodule.finrank_eq_zero]
  unfold Matrix.rank
  omega

end Rank

/-! ### The reference treatment and the reduced design -/

section Reduced

variable {E K : Type*} [DecidableEq K]

/-- The **padded level vector** of the basic parameters `d_k`, `k ≠ r`: the value `0` at the
reference treatment `r` and `d_k` elsewhere. -/
def padReference (r : K) (d : {k // k ≠ r} → ℝ) (k : K) : ℝ :=
  if h : k = r then 0 else d ⟨k, h⟩

@[simp] theorem padReference_self (r : K) (d : {k // k ≠ r} → ℝ) : padReference r d r = 0 := by
  simp [padReference]

theorem padReference_of_ne {r k : K} (h : k ≠ r) (d : {k // k ≠ r} → ℝ) :
    padReference r d k = d ⟨k, h⟩ := by
  simp [padReference, h]

@[simp] theorem padReference_val {r : K} (d : {k // k ≠ r} → ℝ) (k : {k // k ≠ r}) :
    padReference r d k.1 = d k :=
  padReference_of_ne k.2 d

/-- Padding then restricting returns the basic parameters. -/
theorem padReference_restrict {r : K} {θ : K → ℝ} (hθ : θ r = 0) :
    padReference r (fun k => θ k.1) = θ := funext fun k => by
  by_cases h : k = r
  · subst h; simp [hθ]
  · simp [padReference_of_ne h]

theorem padReference_injective (r : K) : Function.Injective (padReference r) := fun d d' h =>
  funext fun k => by simpa using congrFun h k.1

theorem padReference_add (r : K) (d d' : {k // k ≠ r} → ℝ) :
    padReference r (d + d') = padReference r d + padReference r d' := by
  funext k; by_cases h : k = r <;> simp [padReference, h]

theorem padReference_smul (r : K) (c : ℝ) (d : {k // k ≠ r} → ℝ) :
    padReference r (c • d) = c • padReference r d := by
  funext k; by_cases h : k = r <;> simp [padReference, h]

/-- The **reduced design** with reference treatment `r`: the columns `k ≠ r` of the incidence
matrix. Its parameters are the basic parameters `d_k = θ_k - θ_r`. -/
def reducedDesign (tail head : E → K) (r : K) : Matrix E {k // k ≠ r} ℝ :=
  Matrix.of fun e k => incidenceMatrix tail head e k.1

variable [Fintype K]

/-- The reduced design applied to the basic parameters is the incidence matrix applied to the
padded level vector: `(X d)_e = d̃_{head e} - d̃_{tail e}`. -/
theorem reducedDesign_mulVec (tail head : E → K) (r : K) (d : {k // k ≠ r} → ℝ) :
    reducedDesign tail head r *ᵥ d = incidenceMatrix tail head *ᵥ padReference r d := by
  funext e
  simp only [mulVec, dotProduct, reducedDesign, Matrix.of_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ r, padReference_self, mul_zero, zero_add]
  simp

theorem reducedDesign_mulVec_apply (tail head : E → K) (r : K) (d : {k // k ≠ r} → ℝ) (e : E) :
    (reducedDesign tail head r *ᵥ d) e = padReference r d (head e) - padReference r d (tail e) := by
  rw [reducedDesign_mulVec, incidenceMatrix_mulVec]

/-- **The reduced design has full column rank exactly for a connected network**: with a
reference treatment `r`, `d ↦ X d` is injective if and only if the comparison graph is
connected. If it is connected, a kernel vector pads to a level vector constant on the whole
graph and zero at `r`; if not, the indicator of a component missing `r` is a nonzero kernel
vector. -/
theorem reducedDesign_injective_iff (tail head : E → K) (r : K) :
    Function.Injective (reducedDesign tail head r).mulVec ↔
      (comparisonGraph tail head).Connected := by
  classical
  set G := comparisonGraph tail head
  have : Nonempty K := ⟨r⟩
  constructor
  · intro hinj
    by_contra hcon
    have hk : ∃ k, ¬G.Reachable r k := by
      by_contra h
      push Not at h
      exact hcon ⟨fun a b => (h a).symm.trans (h b)⟩
    obtain ⟨k, hk⟩ := hk
    have hkr : k ≠ r := fun h => hk (h ▸ SimpleGraph.Reachable.refl _)
    let d : {k // k ≠ r} → ℝ := fun x => if G.Reachable k x.1 then 1 else 0
    have hpad : padReference r d = fun x => if G.Reachable k x then 1 else 0 := by
      funext x
      by_cases hx : x = r
      · subst hx
        have hkx : ¬G.Reachable k x := fun h => hk h.symm
        simp [hkx]
      · simp [padReference_of_ne hx, d]
    have hker : reducedDesign tail head r *ᵥ d = reducedDesign tail head r *ᵥ 0 := by
      rw [mulVec_zero, reducedDesign_mulVec, hpad,
        incidenceMatrix_mulVec_eq_zero_iff_reachable]
      intro a b hab
      by_cases ha : G.Reachable k a
      · simp [ha, ha.trans hab]
      · have hb : ¬G.Reachable k b := fun h => ha (h.trans hab.symm)
        simp [ha, hb]
    have := congrFun (hinj hker) ⟨k, hkr⟩
    simp [d] at this
  · intro hcon d d' h
    have h0 : incidenceMatrix tail head *ᵥ padReference r (d - d') = 0 := by
      rw [← reducedDesign_mulVec, mulVec_sub, h, sub_self]
    rw [incidenceMatrix_mulVec_eq_zero_iff_reachable] at h0
    funext k
    have := h0 r k.1 (hcon.preconnected r k.1)
    simp only [padReference_self, padReference_val, Pi.sub_apply] at this
    linarith

/-- With a reference treatment removed, `T - 1` columns remain (stated additively). -/
theorem card_ne_reference_add_one (r : K) : Fintype.card {k // k ≠ r} + 1 = Fintype.card K := by
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ r),
    Finset.card_univ]
  have := Fintype.card_pos_iff.2 ⟨r⟩
  omega

/-- **Rank of the reduced design**: `rank X = T - 1` (stated as `rank X + 1 = T`) if and only
if the network is connected. -/
theorem rank_reducedDesign_iff (tail head : E → K) (r : K) :
    (reducedDesign tail head r).rank + 1 = Fintype.card K ↔
      (comparisonGraph tail head).Connected := by
  have h1 := card_ne_reference_add_one r
  rw [← reducedDesign_injective_iff tail head r, ← rank_eq_card_iff_injective_mulVec]
  omega

/-- **The reduced design has the rank of the incidence matrix**: dropping the reference column
does not change the column space, since every contrast vector `B θ` equals `B (θ - θ_r)`. -/
theorem rank_reducedDesign (tail head : E → K) (r : K) :
    (reducedDesign tail head r).rank = (incidenceMatrix tail head).rank := by
  have h : LinearMap.range (reducedDesign tail head r).mulVecLin =
      LinearMap.range (incidenceMatrix tail head).mulVecLin := by
    ext δ
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨padReference r d, (reducedDesign_mulVec tail head r d).symm⟩
    · rintro ⟨θ, rfl⟩
      refine ⟨fun k => θ k.1 - θ r, ?_⟩
      rw [reducedDesign_mulVec,
        padReference_restrict (θ := fun k => θ k - θ r) (by simp)]
      funext e
      rw [incidenceMatrix_mulVec, incidenceMatrix_mulVec]
      ring
  rw [Matrix.rank, Matrix.rank, h]

end Reduced

end NetworkMetaAnalysis

end CausalInference
