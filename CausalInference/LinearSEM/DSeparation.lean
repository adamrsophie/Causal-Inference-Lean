/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.SingleDoor
public import CausalInference.Graphical.Criteria.Moralization

/-!
# d-separation and vanishing partial covariance in linear SEMs

For a recursive linear SEM with uncorrelated errors (diagonal error covariance `Ω`), d-separation
of `a` and `b` by `Z` in the causal graph implies that the partial covariance of `X a` and `X b`
given `X_Z` vanishes, whenever the covariance block of `Z` is invertible. With this bridge the
single-door criterion (Pearl 2009, Theorem 5.3.1) and the linear back-door criterion (Pearl 2009,
Theorem 5.3.2) are proved in graphical form for uncorrelated errors.

## Main results

* `LinearSEM.partialCov_eq_zero_of_dSep`: `G.DSep {a} {b} Z` implies
  `partialCov Σ Z a b = 0`, for diagonal `Ω` and invertible `Σ_ZZ`. No positivity of the error
  variances is needed beyond positive semidefiniteness.
* `LinearSEM.single_door`: the single-door criterion (Theorem 5.3.1) in graphical form, for
  diagonal `Ω`: `α = r_YX·Z` when `Z` has no descendant of `y` and d-separates `x` from `y` in
  `G_α` (`LinearSEM.deleteEdgeGraph`).
* `LinearSEM.back_door`: the linear back-door criterion (Theorem 5.3.2), for diagonal `Ω`: the
  total effect `T y x = r_YX·Z` when `Z` has no descendant of `x` and d-separates `x` from `y` in
  `G_x̲`. The proof uses the decomposition `LinearSEM.isRegCoeff_cutOutgoing_add` of the
  regression through the model `LinearSEM.cutOutgoing x` without the arrows out of `x`.
* `LinearSEM.DescendantExample.dSep_deleteEdgeGraph`,
  `LinearSEM.DescendantExample.counterexample_single_door`: in the chain `X → Y → Z`, with
  `Z = {Z}`, every hypothesis of `single_door` other than the absence of descendants of `Y` from
  `Z` holds (the d-separation in `G_α` included), and the conclusion fails.

Correlated errors are not covered: for them d-separation in the directed graph does not imply a
vanishing partial covariance (see `LinearSEM.single_door_of_partialCov`). Path diagrams with
bidirected arcs, read as latent common causes, are treated in
`CausalInference.LinearSEM.CorrelatedErrors`, and the measure-zero converse of the single-door
criterion for three failure patterns is in `CausalInference.LinearSEM.SingleDoorConverse`.

## Proof outline

By the ancestral moralization criterion (`Digraph.dSep_iff_moralSep`), `Z` separates `a` from `b`
in the moral graph of the subgraph on the ancestral set `S` of `{a, b} ∪ Z`. Let `r` be the
coefficient vector of the residual of the regression of `X b` on `X_Z`, `w = Σ r` (so that
`w a` is the partial covariance and `w` vanishes on `Z`) and `u = Tᵀ r`. Then `(1 - B) w = Ω u`,
`(1 - B)ᵀ u = r`, and `u` vanishes outside `S`. Let `D` be the set of vertices joined to `a` in the
moral graph by a path avoiding `Z`, and `w'` the restriction of `w` to `D`. For `k ∈ S` the family
of `k` (itself and its parents) is a clique of the moral graph, so `((1 - B) w') k` is either
`0` or `((1 - B) w) k = Ω k k u k`. The quadratic form
`0 = w' ⬝ r = ∑ k, ((1 - B) w') k u k` is a sum of the nonnegative terms `Ω k k (u k)²`, so
`(1 - B) w'` vanishes on `S`, and then so does `w' = T (1 - B) w'`; in particular `w a = 0`.

Source: J. Pearl (2009), *Causality*, 2nd edition, Section 5.3.1, Theorems 5.3.1 and 5.3.2;
S. L. Lauritzen, A. P. Dawid, B. N. Larsen and H.-G. Leimer (1990), Independence properties of
directed Markov fields, *Networks* 20.
-/

@[expose] public section

namespace CausalInference

namespace LinearSEM

open Matrix Finset Relation Digraph

variable {V : Type*} [Fintype V] [DecidableEq V] (M : LinearSEM V)

/-- The bridge from d-separation to vanishing partial covariance: in a linear SEM with
uncorrelated errors (diagonal `Ω`), if `a` and `b` are d-separated by `Z` in the causal graph and
the covariance block of `Z` is invertible, then the partial covariance of `X a` and `X b` given
`X_Z` vanishes. -/
theorem partialCov_eq_zero_of_dSep (hΩ : M.Ω.IsDiag) {a b : V} {Z : Finset V}
    (hsep : M.G.DSep {a} {b} ↑Z) (hu : IsUnit (subCov M.cov Z)) :
    partialCov M.cov Z a b = 0 := by
  classical
  have hγ := regCoeff_isRegCoeff b hu
  by_cases haZ : a ∈ Z
  · rw [partialCov, hγ.2 a haZ, sub_self]
  by_cases hbZ : b ∈ Z
  · rw [partialCov_comm M.cov_transpose hu, partialCov, (regCoeff_isRegCoeff a hu).2 b hbZ,
      sub_self]
  set S : Set V := M.G.ancestorsOf ({a} ∪ {b} ∪ ↑Z) with hS
  set H := (M.G.restrict S).moralGraph with hH
  have hms : ¬ ReflTransGen (avoidGraph H ↑Z).Adj a b :=
    (dSep_iff_moralSep.1 hsep) a rfl b rfl (by simpa using haZ)
  set D : Set V := {i | ReflTransGen (avoidGraph H ↑Z).Adj a i} with hD
  have hDZ : ∀ i ∈ D, i ∉ Z := by
    intro i hi
    induction hi with
    | refl => exact haZ
    | tail _ h _ => simpa using h.2.2
  have haS : a ∈ S := subset_ancestorsOf _ (by simp)
  -- the residual `r`, the vectors `w = Σ r`, `u = Tᵀ r`, and `w` restricted to `D`
  obtain ⟨r, hr⟩ : ∃ r : V → ℝ, r = Pi.single b 1 - regCoeff M.cov Z b := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : V → ℝ, w = M.cov *ᵥ r := ⟨_, rfl⟩
  obtain ⟨u, hu'⟩ : ∃ u : V → ℝ, u = M.Tᵀ *ᵥ r := ⟨_, rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : V → ℝ, w' = fun i => if i ∈ D then w i else 0 := ⟨_, rfl⟩
  have hwv : ∀ s, w s = M.cov s b - ∑ t, M.cov s t * regCoeff M.cov Z b t := by
    intro s
    rw [hw, hr]
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    simp [Pi.single_apply]
  have hwa : partialCov M.cov Z a b = w a := by rw [hwv, partialCov]
  have hwZ : ∀ s ∈ Z, w s = 0 := fun s hs => by rw [hwv, hγ.2 s hs, sub_self]
  have hBw : (1 - M.B) *ᵥ w = M.Ω *ᵥ u := by
    rw [hw, hu', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, cov, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, M.one_sub_B_mul_T, Matrix.one_mul]
  have hBu : (1 - M.B)ᵀ *ᵥ u = r := by
    rw [hu', Matrix.mulVec_mulVec, ← Matrix.transpose_mul, M.T_mul_one_sub_B,
      Matrix.transpose_one, Matrix.one_mulVec]
  -- `u` vanishes outside the ancestral set
  have huS : ∀ k ∉ S, u k = 0 := by
    intro k hk
    rw [hu']
    refine Finset.sum_eq_zero fun i _ => ?_
    change M.Tᵀ k i * r i = 0
    rw [Matrix.transpose_apply]
    by_cases hT : M.T i k = 0
    · rw [hT, zero_mul]
    by_cases hri : r i = 0
    · rw [hri, mul_zero]
    exfalso
    refine hk (mem_ancestorsOf.2 ⟨i, ?_, M.T_apply_ne_zero hT⟩)
    by_cases hib : i = b
    · simp [hib]
    · have hiZ : i ∈ Z := by
        by_contra hiZ
        exact hri (by simp [hr, hib, hγ.1 i hiZ])
      simp [hiZ]
  -- `r` vanishes on `D`
  have hrD : ∀ i ∈ D, r i = 0 := by
    intro i hi
    have hib : i ≠ b := fun h => hms (h ▸ hi)
    simp [hr, hib, hγ.1 i (hDZ i hi)]
  -- the family of `k ∈ S` is a clique of the moral graph
  have hfam : ∀ k ∈ S, ∀ m j, (m = k ∨ M.B k m ≠ 0) → (j = k ∨ M.B k j ≠ 0) → m ∈ D →
      j ∉ Z → j ∈ D := by
    intro k hk m j hm hj hmD hjZ
    by_cases hmj : m = j
    · exact hmj ▸ hmD
    have hpar : ∀ p, M.B k p ≠ 0 → (M.G.restrict S).Adj p k := fun p hp =>
      ⟨M.B_support k p hp, mem_ancestorsOf_of_adj (M.B_support k p hp) hk, hk⟩
    have hadj : H.Adj m j := by
      rcases hm with rfl | hm <;> rcases hj with rfl | hj
      · exact absurd rfl hmj
      · exact (moralGraph_adj_of_adj (hpar j hj) (Ne.symm hmj)).symm
      · exact moralGraph_adj_of_adj (hpar m hm) hmj
      · exact moralGraph_adj_of_coparents (hpar m hm) (hpar j hj) hmj
    exact ReflTransGen.tail hmD ⟨hadj, by simpa using hDZ m hmD, by simpa using hjZ⟩
  have hsub : ∀ v : V → ℝ, ∀ k, ((1 - M.B) *ᵥ v) k = v k - ∑ p, M.B k p * v p := by
    intro v k
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
    rfl
  have hclique : ∀ k ∈ S, ((1 - M.B) *ᵥ w') k = 0 ∨
      ((1 - M.B) *ᵥ w') k = ((1 - M.B) *ᵥ w) k := by
    intro k hk
    by_cases hex : k ∈ D ∨ ∃ p, M.B k p ≠ 0 ∧ p ∈ D
    · right
      obtain ⟨m, hm, hmD⟩ : ∃ m, (m = k ∨ M.B k m ≠ 0) ∧ m ∈ D := by
        rcases hex with h | ⟨p, hp, hpD⟩
        · exact ⟨k, Or.inl rfl, h⟩
        · exact ⟨p, Or.inr hp, hpD⟩
      have heq : ∀ j, (j = k ∨ M.B k j ≠ 0) → w' j = w j := by
        intro j hj
        rw [hw']
        by_cases hjD : j ∈ D
        · simp [hjD]
        · have hjZ : j ∈ Z := by
            by_contra hjZ
            exact hjD (hfam k hk m j hm hj hmD hjZ)
          simp [hjD, hwZ j hjZ]
      rw [hsub, hsub, heq k (Or.inl rfl)]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : M.B k p = 0
      · rw [hp, zero_mul, zero_mul]
      · rw [heq p (Or.inr hp)]
    · left
      simp only [not_or, not_exists, not_and] at hex
      rw [hsub]
      have hk0 : w' k = 0 := by rw [hw']; simp [hex.1]
      rw [hk0, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun p _ => ?_
      by_cases hp : M.B k p = 0
      · rw [hp, zero_mul]
      · have : w' p = 0 := by rw [hw']; simp [hex.2 p hp]
        rw [this, mul_zero]
  have hΩu : ∀ k, (M.Ω *ᵥ u) k = M.Ω k k * u k := by
    intro k
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single k]
    · intro j _ hj
      rw [hΩ (Ne.symm hj), zero_mul]
    · simp
  -- the quadratic form
  have hdot : ∑ k, ((1 - M.B) *ᵥ w') k * u k = 0 := by
    have h1 : w' ⬝ᵥ r = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hw']
      by_cases hiD : i ∈ D
      · simp [hiD, hrD i hiD]
      · simp [hiD]
    rw [← hBu, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at h1
    simpa [dotProduct] using h1
  have hterm : ∀ k, 0 ≤ ((1 - M.B) *ᵥ w') k * u k := by
    intro k
    by_cases hk : k ∈ S
    · rcases hclique k hk with h | h
      · rw [h, zero_mul]
      · rw [h, hBw, hΩu, mul_assoc]
        exact mul_nonneg M.Ω_posSemidef.diag_nonneg (mul_self_nonneg _)
    · rw [huS k hk, mul_zero]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hterm k).1 hdot
  have hvS : ∀ k ∈ S, ((1 - M.B) *ᵥ w') k = 0 := by
    intro k hk
    rcases hclique k hk with h | h
    · exact h
    · have h0 := hzero k (Finset.mem_univ k)
      have hv : ((1 - M.B) *ᵥ w') k = M.Ω k k * u k := by rw [h, hBw, hΩu]
      have : ((1 - M.B) *ᵥ w') k * ((1 - M.B) *ᵥ w') k = 0 := by
        calc ((1 - M.B) *ᵥ w') k * ((1 - M.B) *ᵥ w') k
            = M.Ω k k * (((1 - M.B) *ᵥ w') k * u k) := by rw [hv]; ring
          _ = 0 := by rw [h0, mul_zero]
      exact mul_self_eq_zero.1 this
  -- `w' = T (1 - B) w'` vanishes on the ancestral set
  have hw'S : ∀ i ∈ S, w' i = 0 := by
    intro i hi
    have hT : w' = M.T *ᵥ ((1 - M.B) *ᵥ w') := by
      rw [Matrix.mulVec_mulVec, M.T_mul_one_sub_B, Matrix.one_mulVec]
    rw [hT]
    refine Finset.sum_eq_zero fun k _ => ?_
    change M.T i k * ((1 - M.B) *ᵥ w') k = 0
    by_cases hk : k ∈ S
    · rw [hvS k hk, mul_zero]
    · have : M.T i k = 0 := by
        by_contra h
        exact hk (mem_ancestorsOf_of_reflTransGen (M.T_apply_ne_zero h) hi)
      rw [this, zero_mul]
  have haD : a ∈ D := ReflTransGen.refl
  have := hw'S a haS
  rw [hw'] at this
  simp only [haD, ↓reduceIte] at this
  rw [hwa, this]

/-! ### The single-door criterion in graphical form -/

/-- The graph `G_α` of Theorem 5.3.1: `G` with the edge `x → y` removed. -/
def deleteEdgeGraph (G : Digraph V) (x y : V) : Digraph V where
  Adj u v := G.Adj u v ∧ ¬ (u = x ∧ v = y)

/-- The model `M` with the coefficient of `x → y` set to zero and the edge `x → y` removed from the
graph: the model `deleteCoeff` with graph `G_α`. Its covariance matrix is that of `deleteCoeff`
(`deleteEdge_cov`). -/
def deleteEdge (y x : V) : LinearSEM V where
  G := deleteEdgeGraph M.G x y
  acyclic := M.acyclic.anti fun _ _ h => h.1
  B := (M.deleteCoeff y x).B
  B_support v u h := by
    refine ⟨(M.deleteCoeff y x).B_support v u h, ?_⟩
    rintro ⟨rfl, rfl⟩
    exact h (by simp [deleteCoeff_B_apply])
  Ω := M.Ω
  Ω_posSemidef := M.Ω_posSemidef

theorem deleteEdge_cov (y x : V) : (M.deleteEdge y x).cov = (M.deleteCoeff y x).cov := rfl

/-- The single-door criterion (Pearl 2009, Theorem 5.3.1) for uncorrelated errors: let `x → y` be
an edge of `G` with path coefficient `α = B y x`, and let `Z` be a set of variables, none of them a
descendant of `y`, that d-separates `x` from `y` in the graph `G_α` obtained by deleting the edge
`x → y`. If `Ω` is diagonal and the covariance blocks of `Z` and of `insert x Z` are invertible,
then `α` is the coefficient of `x` in the population regression of `y` on `x` and `Z`:
`α = r_YX·Z`. (The converse part of the theorem, that `r_YX·Z` is not consistent for `α` when
the conditions fail, is not formalized.) -/
theorem single_door (hΩ : M.Ω.IsDiag) {x y : V} {Z : Finset V} (hxy : M.G.Adj x y)
    (hxZ : x ∉ Z) (hZ : ∀ s ∈ Z, ¬ ReflTransGen M.G.Adj y s)
    (hsep : (deleteEdgeGraph M.G x y).DSep {x} {y} ↑Z)
    (huZ : IsUnit (subCov M.cov Z)) (hu : IsUnit (subCov M.cov (insert x Z))) :
    regCoeff M.cov (insert x Z) y x = M.B y x := by
  have hS : ∀ s ∈ insert x Z, ¬ ReflTransGen M.G.Adj y s := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact M.not_reflTransGen_of_adj hxy
    · exact hZ s hs
  have huZ' : IsUnit (subCov (M.deleteEdge y x).cov Z) := by
    rw [deleteEdge_cov, M.subCov_deleteCoeff hZ]
    exact huZ
  refine M.single_door_of_partialCov hxZ hS huZ hu ?_
  rw [← deleteEdge_cov]
  exact (M.deleteEdge y x).partialCov_eq_zero_of_dSep hΩ hsep huZ'

/-! ### The linear back-door criterion -/

/-- The model `M` with every arrow out of `x` removed: column `x` of `B` is set to zero, and the
graph is `G_x̲` (`Digraph.deleteOutgoing`). -/
def cutOutgoing (x : V) : LinearSEM V where
  G := M.G.deleteOutgoing {x}
  acyclic := M.acyclic.deleteOutgoing
  B := fun i j => if j = x then 0 else M.B i j
  B_support v u h := by
    by_cases hu : u = x
    · simp [hu] at h
    · simp only [hu, ite_false] at h
      exact (deleteOutgoing_adj).2 ⟨M.B_support v u h, by simpa using hu⟩
  Ω := M.Ω
  Ω_posSemidef := M.Ω_posSemidef

theorem cutOutgoing_B_apply (x i j : V) :
    (M.cutOutgoing x).B i j = if j = x then 0 else M.B i j := rfl

/-- `T - T' = T (B - B') T'`, where `T'` and `B'` are those of `cutOutgoing x`. -/
theorem T_sub_T_cutOutgoing (x : V) :
    M.T - (M.cutOutgoing x).T = M.T * (M.B - (M.cutOutgoing x).B) * (M.cutOutgoing x).T := by
  calc M.T - (M.cutOutgoing x).T
      = M.T * ((1 - (M.cutOutgoing x).B) * (M.cutOutgoing x).T) -
          (M.T * (1 - M.B)) * (M.cutOutgoing x).T := by
        rw [(M.cutOutgoing x).one_sub_B_mul_T, M.T_mul_one_sub_B, Matrix.mul_one, Matrix.one_mul]
    _ = M.T * (M.B - (M.cutOutgoing x).B) * (M.cutOutgoing x).T := by noncomm_ring

/-- Entry `(s, j)` of `T (B - B')`: zero unless `j = x`, where it is `(T B) s x`. -/
theorem T_mul_B_sub_cutOutgoing_apply (x s j : V) :
    (M.T * (M.B - (M.cutOutgoing x).B)) s j = if j = x then (M.T * M.B) s x else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : j = x
  · subst hj
    simp [cutOutgoing_B_apply, Matrix.mul_apply]
  · simp [cutOutgoing_B_apply, hj]

/-- `(T B) s x = 0` unless `s` is a strict descendant of `x`. -/
theorem T_mul_B_apply_eq_zero {x s : V} (hs : ¬ TransGen M.G.Adj x s) : (M.T * M.B) s x = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hB : M.B i x = 0
  · rw [hB, mul_zero]
  by_cases hT : M.T s i = 0
  · rw [hT, zero_mul]
  exact absurd (TransGen.head' (M.B_support i x hB) (M.T_apply_ne_zero hT)) hs

/-- Cutting the arrows out of `x` does not change the total effects on a variable `s` that is not
a strict descendant of `x` (in particular on `x` itself). -/
theorem T_cutOutgoing_apply {x s : V} (hs : ¬ TransGen M.G.Adj x s) (k : V) :
    (M.cutOutgoing x).T s k = M.T s k := by
  have h := congrFun (congrFun (M.T_sub_T_cutOutgoing x) s) k
  rw [Matrix.sub_apply, Matrix.mul_apply] at h
  simp only [T_mul_B_sub_cutOutgoing_apply, M.T_mul_B_apply_eq_zero hs, ite_self, zero_mul,
    Finset.sum_const_zero] at h
  linarith

/-- The decomposition of total effects through `x`: for `v ≠ x`,
`T v k = T' v k + T v x T x k`, where `T'` is the total effect matrix of `cutOutgoing x`. -/
theorem T_eq_cutOutgoing_add {x v : V} (hv : v ≠ x) (k : V) :
    M.T v k = (M.cutOutgoing x).T v k + M.T v x * M.T x k := by
  have h := congrFun (congrFun (M.T_sub_T_cutOutgoing x) v) k
  rw [Matrix.sub_apply, Matrix.mul_apply] at h
  simp only [T_mul_B_sub_cutOutgoing_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  have hTB : (M.T * M.B) v x = M.T v x := by
    have := congrFun (congrFun M.T_eq_one_add_T_mul_B v) x
    rw [Matrix.add_apply, Matrix.one_apply_ne hv] at this
    linarith
  rw [hTB, M.T_cutOutgoing_apply (M.acyclic x) k] at h
  linarith

/-- Covariances among variables that are not strict descendants of `x` are unchanged by cutting
the arrows out of `x`. -/
theorem cov_cutOutgoing {x s t : V} (hs : ¬ TransGen M.G.Adj x s)
    (ht : ¬ TransGen M.G.Adj x t) : (M.cutOutgoing x).cov s t = M.cov s t := by
  rw [cov_apply, cov_apply]
  simp only [M.T_cutOutgoing_apply hs, M.T_cutOutgoing_apply ht]
  rfl

/-- The covariance with `y ≠ x` splits as the covariance in the model without the arrows out of
`x` plus `T y x Σ s x`, for every `s` that is not a strict descendant of `x`. -/
theorem cov_eq_cov_cutOutgoing_add {x y s : V} (hy : y ≠ x) (hs : ¬ TransGen M.G.Adj x s) :
    M.cov s y = (M.cutOutgoing x).cov s y + M.T y x * M.cov s x := by
  have hΩ' : (M.cutOutgoing x).Ω = M.Ω := rfl
  rw [cov_apply, cov_apply, cov_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [M.T_eq_cutOutgoing_add hy b, M.T_cutOutgoing_apply hs a, hΩ']
  ring

/-- The back-door decomposition `r_YX·S = T y x + r'_YX·S`: let `x ∈ S`, `y ≠ x`, and let no
variable of `S` be a strict descendant of `x`. If `γ` are the regression coefficients of `y` on
`S` in the model without the arrows out of `x`, then `γ + T y x e_x` are the regression
coefficients of `y` on `S` in the model itself. -/
theorem isRegCoeff_cutOutgoing_add {x y : V} {S : Finset V} (hx : x ∈ S) (hy : y ≠ x)
    (hS : ∀ s ∈ S, ¬ TransGen M.G.Adj x s) {γ : V → ℝ}
    (hγ : IsRegCoeff (M.cutOutgoing x).cov S y γ) :
    IsRegCoeff M.cov S y (γ + M.T y x • Pi.single x 1) := by
  refine ⟨fun v hv => ?_, fun s hs => ?_⟩
  · have hvx : v ≠ x := fun h => hv (h ▸ hx)
    simp [hγ.1 v hv, hvx]
  · have h1 : ∀ t, M.cov s t * (γ + M.T y x • Pi.single x 1 : V → ℝ) t =
        (M.cutOutgoing x).cov s t * γ t +
          M.T y x * (M.cov s t * (Pi.single x 1 : V → ℝ) t) := by
      intro t
      by_cases ht : t ∈ S
      · rw [M.cov_cutOutgoing (hS s hs) (hS t ht)]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · have htx : t ≠ x := fun h => ht (h ▸ hx)
        simp [hγ.1 t ht, htx]
    simp only [h1, Finset.sum_add_distrib, hγ.2 s hs, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [M.cov_eq_cov_cutOutgoing_add hy (hS s hs)]

/-- The linear back-door criterion (Pearl 2009, Theorem 5.3.2) for uncorrelated errors: if no
member of `Z` is a descendant of `x` and `Z` d-separates `x` from `y` in the graph `G_x̲` obtained
by deleting every arrow out of `x`, then, with diagonal `Ω` and invertible covariance blocks of
`Z` and of `insert x Z`, the coefficient of `x` in the population regression of `y` on `x` and
`Z` is the total effect `T y x` of `x` on `y`: `T y x = r_YX·Z`. -/
theorem back_door (hΩ : M.Ω.IsDiag) {x y : V} {Z : Finset V}
    (hZ : ∀ s ∈ Z, ¬ ReflTransGen M.G.Adj x s)
    (hsep : (M.G.deleteOutgoing {x}).DSep {x} {y} ↑Z)
    (huZ : IsUnit (subCov M.cov Z)) (hu : IsUnit (subCov M.cov (insert x Z))) :
    regCoeff M.cov (insert x Z) y x = M.T y x := by
  have hxZ : x ∉ Z := fun h => hZ x h ReflTransGen.refl
  have hy : y ≠ x := by
    rintro rfl
    exact hsep ⟨y, rfl, y, rfl, by simpa using hxZ, by simpa using hxZ, false, ReflTransGen.refl⟩
  have hS : ∀ s ∈ insert x Z, ¬ TransGen M.G.Adj x s := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact M.acyclic s
    · exact fun h => hZ s hs h.to_reflTransGen
  have hsub : ∀ S : Finset V, (∀ s ∈ S, ¬ TransGen M.G.Adj x s) →
      subCov (M.cutOutgoing x).cov S = subCov M.cov S := fun S hS' => by
    ext s t
    exact M.cov_cutOutgoing (hS' s s.2) (hS' t t.2)
  have hSZ : ∀ s ∈ Z, ¬ TransGen M.G.Adj x s := fun s hs => hS s (Finset.mem_insert_of_mem hs)
  have huZ' : IsUnit (subCov (M.cutOutgoing x).cov Z) := by rwa [hsub Z hSZ]
  have hu' : IsUnit (subCov (M.cutOutgoing x).cov (insert x Z)) := by rwa [hsub _ hS]
  have hγ := regCoeff_isRegCoeff y hu'
  have hβ := M.isRegCoeff_cutOutgoing_add (Finset.mem_insert_self x Z) hy hS hγ
  rw [← hβ.unique hu (regCoeff_isRegCoeff y hu)]
  have h0 : partialCov (M.cutOutgoing x).cov Z x y = 0 :=
    (M.cutOutgoing x).partialCov_eq_zero_of_dSep hΩ hsep huZ'
  have hzero := (hγ.eq_zero_iff_partialCov_eq_zero hxZ huZ' hu').2 h0
  simp [hzero]


/-! ### The descendant example in graphical form -/

namespace DescendantExample

open Relation

/-- In the chain `X → Y → Z` of `DescendantExample`, deleting the edge `X → Y` isolates `X`, so
`X` and `Y` are d-separated by `{Z}` in `G_α`. -/
theorem dSep_deleteEdgeGraph :
    (deleteEdgeGraph model.G 0 1).DSep {0} {1} ↑({2} : Finset (Fin 3)) := by
  rintro ⟨x, hx, y, hy, -, -, b, h⟩
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx hy
  rcases ReflTransGen.cases_head h with h | ⟨⟨w, c⟩, hstep, -⟩
  · simp at h
  · have hA := hstep.1
    cases c <;> simp [deleteEdgeGraph, model, G] at hA

/-- The condition of `single_door` that `Z` contains no descendant of `y` cannot be dropped. In
`DescendantExample.model` (diagonal `Ω`), with `x = X`, `y = Y` and `Z = {Z}`, every other
hypothesis of `single_door` holds: `X → Y` is an edge, `X ∉ Z`, `Z` d-separates `X` from `Y` in
`G_α`, and both covariance blocks are invertible. But `Z` is a descendant of `Y`, and the
coefficient of `X` in the regression of `Y` on `X` and `Z` is `1 / 2`, not the path coefficient
`1`. -/
theorem counterexample_single_door :
    model.Ω.IsDiag ∧ model.G.Adj 0 1 ∧ (0 : Fin 3) ∉ ({2} : Finset (Fin 3)) ∧
      (deleteEdgeGraph model.G 0 1).DSep {0} {1} ↑({2} : Finset (Fin 3)) ∧
      IsUnit (subCov model.cov {2}) ∧ IsUnit (subCov model.cov (insert 0 {2})) ∧
      ReflTransGen model.G.Adj 1 2 ∧ regCoeff model.cov (insert 0 {2}) 1 0 = 1 / 2 ∧
      model.B 1 0 = 1 ∧ regCoeff model.cov (insert 0 {2}) 1 0 ≠ model.B 1 0 := by
  obtain ⟨-, hu₁, hu₂, hdesc, hr, hB⟩ := counterexample
  refine ⟨Matrix.isDiag_one, Or.inl ⟨rfl, rfl⟩, by decide, dSep_deleteEdgeGraph, hu₁, hu₂, hdesc,
    hr, hB, ?_⟩
  rw [hr, hB]; norm_num

end DescendantExample

end LinearSEM

end CausalInference
