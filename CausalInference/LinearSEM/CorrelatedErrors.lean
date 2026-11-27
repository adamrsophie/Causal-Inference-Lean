/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.DSeparation
public import CausalInference.LinearSEM.Counterexamples
public import CausalInference.Graphical.ADMG
public import Mathlib.Data.Matrix.Block

/-!
# Correlated errors: path diagrams with bidirected arcs

Pearl's path diagrams draw correlated errors as bidirected arcs. This file treats them as
directed mixed graphs (`CausalInference.ADMG`), in the semi-Markovian reading of latent common
causes: a path diagram (`LinearSEM.PathDiagram`) for a linear SEM `M` is a mixed graph `G`
together with a factor representation `Ω = Λ Λᵀ + diag(D)` of the error covariance, in which the
errors are `ε = Λ ℓ + η` with uncorrelated unit-variance latent factors `ℓ (a, b)`, one for each
pair, loading only on `a` and `b` and only along a bidirected edge `a ↔ b`, and uncorrelated
residuals `η` with variances `D ≥ 0`. Every nonzero off-diagonal entry of `Ω` is then covered
by a bidirected edge (`PathDiagram.covers`).

Which models are covered: every model with uncorrelated errors (`PathDiagram.ofIsDiag`), and
every model whose error covariance has such a factor representation along the bidirected edges.
Not every positive semidefinite `Ω` whose off-diagonal support lies in the bidirected edges has
one (a representation with one latent per edge exists, for example, when `Ω` is diagonally
dominant, which is not proved here). The m-separation theorem for arbitrary `Ω` with the given
support, proved by the trek rule in the literature, is not formalized.

m-separation (`ADMG.MSep`) is defined as d-separation of the observed vertices in the canonical
DAG `ADMG.canonicalDAG`, which replaces each bidirected edge `a ↔ b` by a latent common parent
of `a` and `b`. The path definition of m-separation (Richardson 2003) is not in this library,
and its agreement with this definition is not proved here.

## Main definitions

* `ADMG.canonicalDAG G`: the DAG on `V ⊕ V × V` with a latent parent `Sum.inr (a, b)` of
  `Sum.inl a` and `Sum.inl b` for each bidirected edge `a ↔ b`.
* `ADMG.MSep G X Y Z`: m-separation, as d-separation in the canonical DAG.
* `LinearSEM.PathDiagram M`: a path diagram with latent common causes for `M`.
* `LinearSEM.PathDiagram.canonical`: the linear SEM on the canonical DAG with uncorrelated errors.

## Main results

* `LinearSEM.partialCov_map`: partial covariances are transported along an embedding of the
  variables that preserves the covariances.
* `LinearSEM.PathDiagram.canonical_cov_inl`: the canonical model has the observed covariances of
  `M`.
* `LinearSEM.PathDiagram.partialCov_eq_zero_of_mSep`: m-separation of `a` and `b` by `Z` in the
  diagram implies a vanishing partial covariance given `Z`, when `Σ_ZZ` is invertible.
* `LinearSEM.PathDiagram.single_door`, `LinearSEM.PathDiagram.back_door`: the single-door
  criterion (Pearl 2009, Theorem 5.3.1) and the back-door criterion for linear models (Theorem
  5.3.2) on path diagrams with bidirected arcs.
* `LinearSEM.BowDiagram.single_door_needs_bidirected`: in the bow with path coefficient `1`, unit
  error variances and error covariance `1 / 2`, the slope is `3 / 2`; deleting `X → Y` leaves
  `X` and `Y` d-separated in the directed graph but m-connected in the diagram.

Sources: J. Pearl (2009), *Causality*, 2nd edition, Section 5.3.1; T. S. Richardson (2003),
*Markov properties for acyclic directed mixed graphs*.
-/

@[expose] public section

namespace CausalInference

open Matrix Finset Relation

namespace ADMG

variable {V : Type*}

/-- The canonical DAG of a directed mixed graph `G` on `V`, on the vertex type `V ⊕ V × V`: the
observed vertices `Sum.inl v` carry the directed edges of `G`, and for every bidirected edge
`a ↔ b` of `G` the latent vertex `Sum.inr (a, b)` is a common parent of `Sum.inl a` and
`Sum.inl b`. A latent `Sum.inr (a, b)` without a bidirected edge `a ↔ b` is isolated, and no
edge points into a latent vertex. -/
def canonicalDAG (G : ADMG V) : Digraph (V ⊕ V × V) where
  Adj s t := match s, t with
    | .inl u, .inl v => G.directed.Adj u v
    | .inr p, .inl v => G.bidirected.Adj p.1 p.2 ∧ (v = p.1 ∨ v = p.2)
    | _, .inr _ => False

variable {G : ADMG V}

@[simp] theorem canonicalDAG_adj_inl_inl {u v : V} :
    G.canonicalDAG.Adj (.inl u) (.inl v) ↔ G.directed.Adj u v := Iff.rfl

@[simp] theorem canonicalDAG_adj_inr_inl {p : V × V} {v : V} :
    G.canonicalDAG.Adj (.inr p) (.inl v) ↔ G.bidirected.Adj p.1 p.2 ∧ (v = p.1 ∨ v = p.2) :=
  Iff.rfl

@[simp] theorem not_canonicalDAG_adj_inr {s : V ⊕ V × V} {p : V × V} :
    ¬ G.canonicalDAG.Adj s (.inr p) := by
  cases s <;> exact id

/-- The canonical DAG of an acyclic directed mixed graph on a finite vertex type is acyclic. -/
theorem IsAcyclic.canonicalDAG [Finite V] (hG : G.IsAcyclic) : G.canonicalDAG.IsAcyclic := by
  have := Fintype.ofFinite V
  obtain ⟨f, hf⟩ := Digraph.IsAcyclic.exists_adj_lt hG
  refine Digraph.isAcyclic_of_adj_lt (Sum.elim (fun v => f v + 1) fun _ => 0) ?_
  rintro (u | p) (v | q) h
  · exact Nat.succ_lt_succ (hf h)
  · exact absurd h not_canonicalDAG_adj_inr
  · exact Nat.succ_pos _
  · exact absurd h not_canonicalDAG_adj_inr

/-- m-separation of `X` and `Y` given `Z` in a directed mixed graph, defined as d-separation of
the corresponding observed vertices in the canonical DAG `ADMG.canonicalDAG`, where every
bidirected edge is replaced by a latent common parent of its endpoints. This is the definition
used in this library; its agreement with the path definition is not proved. -/
def MSep (G : ADMG V) (X Y Z : Set V) : Prop :=
  G.canonicalDAG.DSep (Sum.inl '' X) (Sum.inl '' Y) (Sum.inl '' Z)

end ADMG

namespace LinearSEM

/-! ### Partial covariances under an embedding of the variables -/

section Embedding

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- If the covariance matrix `C'` on `W` restricts to `C` along an embedding `e : V ↪ W`, then
for an invertible block `C_ZZ` the block of `C'` on `e(Z)` is invertible and partial
covariances are transported: `partialCov C' (e Z) (e x) (e y) = partialCov C Z x y`. -/
theorem partialCov_map (e : V ↪ W) {C : Matrix V V ℝ} {C' : Matrix W W ℝ}
    (hC : ∀ a b, C' (e a) (e b) = C a b) {Z : Finset V} (hu : IsUnit (subCov C Z)) (x y : V) :
    IsUnit (subCov C' (Z.map e)) ∧ partialCov C' (Z.map e) (e x) (e y) = partialCov C Z x y := by
  set σ := Finset.equivMap e Z
  have hsub : subCov C' (Z.map e) = (subCov C Z).submatrix σ.symm σ.symm := by
    ext i j
    obtain ⟨i', rfl⟩ := σ.surjective i
    obtain ⟨j', rfl⟩ := σ.surjective j
    simp [σ, hC]
  have hu' : IsUnit (subCov C' (Z.map e)) := by
    rw [hsub]; exact (Matrix.isUnit_submatrix_equiv _ _).2 hu
  refine ⟨hu', ?_⟩
  set γ := regCoeff C Z y
  have hγ := regCoeff_isRegCoeff y hu
  -- the extension of `γ` by zero
  set γ' : W → ℝ := fun w => ∑ v, if e v = w then γ v else 0
  have hγ'e : ∀ v, γ' (e v) = γ v := by
    intro v
    simp only [γ', e.injective.eq_iff]
    simp
  have hγ'0 : ∀ w, (∀ v, e v ≠ w) → γ' w = 0 := by
    intro w hw
    simp [γ', hw]
  have hsum : ∀ f : W → ℝ, ∑ w, f w * γ' w = ∑ v, f (e v) * γ v := by
    intro f
    simp only [γ', Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hreg : IsRegCoeff C' (Z.map e) (e y) γ' := by
    refine ⟨fun w hw => ?_, fun s hs => ?_⟩
    · by_cases hex : ∃ v, e v = w
      · obtain ⟨v, rfl⟩ := hex
        rw [hγ'e]
        exact hγ.1 v fun h => hw (Finset.mem_map_of_mem e h)
      · exact hγ'0 w fun v h => hex ⟨v, h⟩
    · obtain ⟨s', hs', rfl⟩ := Finset.mem_map.1 hs
      rw [hsum]
      simp only [hC]
      exact hγ.2 s' hs'
  rw [partialCov, partialCov, ← hreg.unique hu' (regCoeff_isRegCoeff (e y) hu'), hsum]
  simp only [hC, γ]

end Embedding

/-! ### Path diagrams with latent common causes -/

section PathDiagram

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A path diagram with correlated errors for the linear SEM `M`, in the semi-Markovian form of
latent common causes. It consists of a directed mixed graph `G` whose directed part is acyclic
and carries every nonzero coefficient of `B`, and a representation of the error covariance
`Ω = Λ Λᵀ + diag(D)`: the errors are `ε = Λ ℓ + η` with uncorrelated unit-variance latent
factors `ℓ p`, one for each index `p = (a, b)`, uncorrelated with the uncorrelated residuals `η`
of variances `D v ≥ 0`. The factor `ℓ (a, b)` loads only on `a` and `b`, and only when `G` has
the bidirected edge `a ↔ b`. In particular `G` has a bidirected edge between any two distinct
variables whose errors are correlated (`PathDiagram.covers`). -/
structure PathDiagram (M : LinearSEM V) where
  /-- The mixed graph of the diagram. -/
  G : ADMG V
  /-- Its directed part is acyclic. -/
  acyclic : G.IsAcyclic
  /-- Every nonzero path coefficient is a directed edge of the diagram. -/
  B_support : ∀ v u, M.B v u ≠ 0 → G.directed.Adj u v
  /-- The loadings of the latent factors: `Λ v (a, b)` is the loading of `ℓ (a, b)` on `ε v`. -/
  Λ : Matrix V (V × V) ℝ
  /-- The factor `ℓ (a, b)` loads only on `a` and `b`, and only along an edge `a ↔ b`. -/
  Λ_support : ∀ v p, Λ v p ≠ 0 → G.bidirected.Adj p.1 p.2 ∧ (v = p.1 ∨ v = p.2)
  /-- The residual variances. -/
  D : V → ℝ
  /-- The residual variances are nonnegative. -/
  D_nonneg : ∀ v, 0 ≤ D v
  /-- The error covariance is that of `Λ ℓ + η`. -/
  Ω_eq : M.Ω = Λ * Λᵀ + diagonal D

namespace PathDiagram

variable {M : LinearSEM V} (F : M.PathDiagram)

/-- Two distinct variables without a bidirected edge have uncorrelated errors. -/
theorem Ω_apply_eq_zero {a b : V} (hab : a ≠ b) (hbi : ¬ F.G.bidirected.Adj a b) :
    M.Ω a b = 0 := by
  rw [F.Ω_eq, Matrix.add_apply, diagonal_apply_ne _ hab, add_zero, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_contra h
  rw [transpose_apply] at h
  obtain ⟨hp, ha⟩ := F.Λ_support a p (left_ne_zero_of_mul h)
  obtain ⟨-, hb⟩ := F.Λ_support b p (right_ne_zero_of_mul h)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hab rfl
  · exact hbi hp
  · exact hbi hp.symm
  · exact hab rfl

/-- A model with uncorrelated errors (diagonal `Ω`) has the path diagram of its own DAG, with
no bidirected edge, no latent factor (`Λ = 0`) and residual variances `D v = Ω v v`. -/
def ofIsDiag (hΩ : M.Ω.IsDiag) : M.PathDiagram where
  G := ADMG.ofDigraph M.G
  acyclic := M.acyclic
  B_support := M.B_support
  Λ := 0
  Λ_support _ _ h := absurd rfl h
  D v := M.Ω v v
  D_nonneg _ := M.Ω_posSemidef.diag_nonneg
  Ω_eq := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hΩ hij, diagonal_apply_ne _ hij]

/-- The bidirected edges of the diagram cover the correlated errors:
`Ω a b ≠ 0 → a = b ∨ a ↔ b`. -/
theorem covers {a b : V} (h : M.Ω a b ≠ 0) : a = b ∨ F.G.bidirected.Adj a b := by
  by_contra hc
  obtain ⟨h1, h2⟩ := not_or.1 hc
  exact h (F.Ω_apply_eq_zero h1 h2)

/-- The canonical linear SEM of the diagram, on the variables `V ⊕ V × V`: the observed equations
`X v = ∑ u, B v u X u + ∑ p, Λ v p ℓ p + η v` and the latent equations `ℓ p = ε p`, with
uncorrelated errors (diagonal error covariance `diag(D, 1)`), over the canonical DAG of `G`. -/
def canonical : LinearSEM (V ⊕ V × V) where
  G := F.G.canonicalDAG
  acyclic := F.acyclic.canonicalDAG
  B := fromBlocks M.B F.Λ 0 0
  B_support := by
    rintro (v | q) (u | p) h
    · exact F.B_support v u (by simpa using h)
    · exact (ADMG.canonicalDAG_adj_inr_inl).2 (F.Λ_support v p (by simpa using h))
    · simp at h
    · simp at h
  Ω := diagonal (Sum.elim F.D 1)
  Ω_posSemidef := PosSemidef.diagonal fun i => by
    rcases i with v | p
    · exact F.D_nonneg v
    · exact zero_le_one

/-- The total effect matrix of the canonical model. -/
theorem canonical_T : F.canonical.T = fromBlocks M.T (M.T * F.Λ) 0 1 := by
  refine T_eq_of_mul_eq_one _ ?_
  have h1 : (1 : Matrix (V ⊕ V × V) (V ⊕ V × V) ℝ) = fromBlocks 1 0 0 1 := fromBlocks_one.symm
  change (1 - fromBlocks M.B F.Λ 0 0) * _ = 1
  rw [h1, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, fromBlocks_multiply]
  have hT := M.one_sub_B_mul_T
  congr 1
  · simpa [sub_eq_add_neg] using hT
  · rw [← Matrix.mul_assoc]
    simp only [← sub_eq_add_neg] at hT ⊢
    simp [hT]
  · simp
  · simp

/-- The canonical model reproduces the covariances of the observed variables:
`Σ' (inl a) (inl b) = Σ a b`. -/
theorem canonical_cov_inl (a b : V) :
    F.canonical.cov (Sum.inl a) (Sum.inl b) = M.cov a b := by
  have hcov : M.cov = M.T * diagonal F.D * M.Tᵀ + M.T * F.Λ * (M.T * F.Λ)ᵀ := by
    rw [cov, F.Ω_eq, transpose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  have hΩ : F.canonical.Ω = fromBlocks (diagonal F.D) 0 0 (diagonal 1) := by
    rw [fromBlocks_diagonal]; rfl
  rw [cov, canonical_T, hΩ, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_apply₁₁, hcov]
  simp

/-- **The bridge from m-separation to vanishing partial covariance** for linear SEMs with
correlated errors given by latent common causes (`PathDiagram`): if `a` and `b` are m-separated
by `Z` in the path diagram and the covariance block of `Z` is invertible, then the partial
covariance of `X a` and `X b` given `X_Z` vanishes. The proof applies
`LinearSEM.partialCov_eq_zero_of_dSep` to the canonical model, which has uncorrelated errors and
the same covariances of the observed variables. -/
theorem partialCov_eq_zero_of_mSep {a b : V} {Z : Finset V} (hsep : F.G.MSep {a} {b} ↑Z)
    (hu : IsUnit (subCov M.cov Z)) : partialCov M.cov Z a b = 0 := by
  obtain ⟨hu', h⟩ := partialCov_map Function.Embedding.inl F.canonical_cov_inl hu a b
  rw [← h]
  refine F.canonical.partialCov_eq_zero_of_dSep (isDiag_diagonal _) ?_ hu'
  simpa [ADMG.MSep, Finset.coe_map, canonical] using hsep

end PathDiagram

/-! ### The single-door and back-door criteria on path diagrams -/

namespace PathDiagram

variable {M : LinearSEM V} (F : M.PathDiagram)

/-- The diagram of a model `M'` with the same error covariance as `M` and coefficients supported
on an acyclic graph `G'`: the mixed graph with directed part `G'` and the bidirected edges and
latent factors of `F`. -/
def transfer {M' : LinearSEM V} (G' : Digraph V) (hG' : G'.IsAcyclic)
    (hB : ∀ v u, M'.B v u ≠ 0 → G'.Adj u v) (hΩ : M'.Ω = M.Ω) : M'.PathDiagram where
  G := ⟨G', F.G.bidirected⟩
  acyclic := hG'
  B_support := hB
  Λ := F.Λ
  Λ_support := F.Λ_support
  D := F.D
  D_nonneg := F.D_nonneg
  Ω_eq := hΩ.trans F.Ω_eq

/-- The model `M` with its graph replaced by the directed part of the diagram. It has the same
coefficients, errors and covariance matrix as `M`. -/
def toModel : LinearSEM V where
  G := F.G.directed
  acyclic := F.acyclic
  B := M.B
  B_support := F.B_support
  Ω := M.Ω
  Ω_posSemidef := M.Ω_posSemidef

theorem toModel_cov : F.toModel.cov = M.cov := rfl

/-- **The single-door criterion** (Pearl 2009, Theorem 5.3.1) for path diagrams with correlated
errors given by latent common causes: let `x → y` be a directed edge of the diagram, let `Z`
contain neither `x` nor a descendant of `y` in the diagram, and let `Z` m-separate `x` from `y`
in the diagram `G_α` obtained by deleting the directed edge `x → y` (the bidirected edges are
kept). If the covariance blocks of `Z` and of `insert x Z` are invertible, the path coefficient
is the partial regression coefficient: `B y x = r_YX·Z`. -/
theorem single_door {x y : V} {Z : Finset V} (hxy : F.G.directed.Adj x y) (hxZ : x ∉ Z)
    (hZ : ∀ s ∈ Z, ¬ ReflTransGen F.G.directed.Adj y s)
    (hsep : (ADMG.mk (deleteEdgeGraph F.G.directed x y) F.G.bidirected).MSep {x} {y} ↑Z)
    (huZ : IsUnit (subCov M.cov Z)) (hu : IsUnit (subCov M.cov (insert x Z))) :
    regCoeff M.cov (insert x Z) y x = M.B y x := by
  set M₀ := F.toModel
  have hS : ∀ s ∈ insert x Z, ¬ ReflTransGen M₀.G.Adj y s := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact M₀.not_reflTransGen_of_adj hxy
    · exact hZ s hs
  have hB : ∀ v u, (M₀.deleteCoeff y x).B v u ≠ 0 → (deleteEdgeGraph F.G.directed x y).Adj u v := by
    intro v u h
    rw [deleteCoeff_B_apply] at h
    split_ifs at h with hh
    · exact absurd rfl h
    · exact ⟨F.B_support v u h, fun h' => hh ⟨h'.2, h'.1⟩⟩
  let F' := F.transfer (M' := M₀.deleteCoeff y x) _
    (Digraph.IsAcyclic.anti (H := deleteEdgeGraph F.G.directed x y) (fun _ _ h => h.1) F.acyclic)
    hB rfl
  have huZ' : IsUnit (subCov (M₀.deleteCoeff y x).cov Z) := by
    rw [M₀.subCov_deleteCoeff fun s hs => hS s (Finset.mem_insert_of_mem hs)]
    exact huZ
  exact M₀.single_door_of_partialCov hxZ hS huZ hu (F'.partialCov_eq_zero_of_mSep hsep huZ')

/-- **The back-door criterion for linear models** (Pearl 2009, Theorem 5.3.2) for path diagrams
with correlated errors given by latent common causes: if no member of `Z` is a descendant of
`x` in the diagram and `Z` m-separates `x` from `y` in the diagram `G_x̲` without the directed
edges out of `x` (`ADMG.deleteOutgoing`), then with invertible covariance blocks of `Z` and of
`insert x Z` the total effect is the partial regression coefficient: `T y x = r_YX·Z`. -/
theorem back_door {x y : V} {Z : Finset V} (hZ : ∀ s ∈ Z, ¬ ReflTransGen F.G.directed.Adj x s)
    (hsep : (F.G.deleteOutgoing {x}).MSep {x} {y} ↑Z)
    (huZ : IsUnit (subCov M.cov Z)) (hu : IsUnit (subCov M.cov (insert x Z))) :
    regCoeff M.cov (insert x Z) y x = M.T y x := by
  set M₀ := F.toModel
  have hxZ : x ∉ Z := fun h => hZ x h ReflTransGen.refl
  have hy : y ≠ x := by
    rintro rfl
    refine hsep ⟨Sum.inl y, Set.mem_image_of_mem _ rfl, Sum.inl y, Set.mem_image_of_mem _ rfl,
      ?_, ?_, false, ReflTransGen.refl⟩ <;> simpa using hxZ
  have hS : ∀ s ∈ insert x Z, ¬ TransGen M₀.G.Adj x s := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact M₀.acyclic s
    · exact fun h => hZ s hs h.to_reflTransGen
  have hsub : ∀ S : Finset V, (∀ s ∈ S, ¬ TransGen M₀.G.Adj x s) →
      subCov (M₀.cutOutgoing x).cov S = subCov M₀.cov S := fun S hS' => by
    ext s t
    exact M₀.cov_cutOutgoing (hS' s s.2) (hS' t t.2)
  have hSZ : ∀ s ∈ Z, ¬ TransGen M₀.G.Adj x s := fun s hs => hS s (Finset.mem_insert_of_mem hs)
  have huZ' : IsUnit (subCov (M₀.cutOutgoing x).cov Z) := by rw [hsub Z hSZ]; exact huZ
  have hu' : IsUnit (subCov (M₀.cutOutgoing x).cov (insert x Z)) := by rw [hsub _ hS]; exact hu
  have hγ := regCoeff_isRegCoeff y hu'
  have hβ := M₀.isRegCoeff_cutOutgoing_add (Finset.mem_insert_self x Z) hy hS hγ
  have hu₀ : IsUnit (subCov M₀.cov (insert x Z)) := hu
  change regCoeff M₀.cov (insert x Z) y x = M₀.T y x
  rw [← hβ.unique hu₀ (regCoeff_isRegCoeff y hu₀)]
  let F' := F.transfer (M' := M₀.cutOutgoing x) _ F.acyclic.deleteOutgoing
    (M₀.cutOutgoing x).B_support rfl
  have h0 : partialCov (M₀.cutOutgoing x).cov Z x y = 0 := F'.partialCov_eq_zero_of_mSep hsep huZ'
  have hzero := (hγ.eq_zero_iff_partialCov_eq_zero hxZ huZ' hu').2 h0
  simp [hzero]

end PathDiagram

end PathDiagram

/-! ### The bow as a path diagram -/

namespace BowDiagram

open Bow

/-- Two latent factors `ℓ (0, 1)` and `ℓ (1, 0)`, each loading `1 / 2` on both `X` and `Y`. -/
noncomputable def Λ : Matrix (Fin 2) (Fin 2 × Fin 2) ℝ := fun _ p => if p.1 ≠ p.2 then 1 / 2 else 0

/-- The bow error covariance with unit variances and `Cov(ε_X, ε_Y) = 1 / 2` is
`Λ Λᵀ + diag(1 / 2, 1 / 2)`. -/
theorem errCov_eq : errCov 1 1 (1 / 2) = Λ * Λᵀ + diagonal fun _ => 1 / 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Λ, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

theorem psd : (errCov 1 1 (1 / 2)).PosSemidef := by
  rw [errCov_eq]
  have h := Matrix.posSemidef_self_mul_conjTranspose Λ
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact h.add (PosSemidef.diagonal fun _ => by norm_num)

/-- The bow `Y = X + ε_Y` with unit error variances and `Cov(ε_X, ε_Y) = 1 / 2`. -/
noncomputable abbrev model : LinearSEM (Fin 2) := Bow.model 1 1 1 (1 / 2) psd

/-- The path diagram of the bow: `X → Y` and `X ↔ Y`. -/
noncomputable def diagram : model.PathDiagram where
  G := ⟨Bow.G, ⊤⟩
  acyclic := model.acyclic
  B_support := model.B_support
  Λ := Λ
  Λ_support v p h := by
    have hp : p.1 ≠ p.2 := by
      by_contra hp
      exact h (by simp [Λ, hp])
    refine ⟨by simpa using hp, ?_⟩
    obtain ⟨a, b⟩ := p
    fin_cases v <;> fin_cases a <;> fin_cases b <;> simp_all
  D := fun _ => 1 / 2
  D_nonneg _ := by norm_num
  Ω_eq := errCov_eq

/-- **The bow shows why bidirected arcs are needed in the single-door criterion.** In the bow
`X → Y`, `X ↔ Y` with path coefficient `1`, unit error variances and `Cov(ε_X, ε_Y) = 1 / 2`, the
regression slope of `Y` on `X` is `3 / 2`, not the path coefficient `1`. After deleting the
directed edge `X → Y`, the directed graph alone d-separates `X` from `Y` by `∅` (so the criterion
read on the directed graph would wrongly accept `Z = ∅`), while the path diagram, which keeps the
arc `X ↔ Y`, does not m-separate them (so `PathDiagram.single_door` does not apply). The other
hypotheses of `PathDiagram.single_door` (the edge `X → Y`, `X ∉ ∅`, invertible blocks) hold. -/
theorem single_door_needs_bidirected :
    diagram.G.directed.Adj 0 1 ∧ (0 : Fin 2) ∉ (∅ : Finset (Fin 2)) ∧
      IsUnit (subCov model.cov ∅) ∧ IsUnit (subCov model.cov (insert 0 ∅)) ∧
      regCoeff model.cov (insert 0 ∅) 1 0 = 3 / 2 ∧ model.B 1 0 = 1 ∧
      (deleteEdgeGraph model.G 0 1).DSep {0} {1} ↑(∅ : Finset (Fin 2)) ∧
      ¬ (ADMG.mk (deleteEdgeGraph diagram.G.directed 0 1) diagram.G.bidirected).MSep {0} {1}
        ↑(∅ : Finset (Fin 2)) := by
  have hpd : (errCov (1 : ℝ) 1 (1 / 2)).PosDef := by
    refine (psd.posDef_iff_det_ne_zero).2 ?_
    simp [Matrix.det_fin_two]; norm_num
  have hu := isUnit_submatrix_of_posDef (model.cov_posDef hpd)
  have hxx : model.cov 0 0 ≠ 0 := by simp [Bow.cov_eq]
  refine ⟨⟨rfl, rfl⟩, by simp, hu _, hu _, ?_, by simp [Bow.model], ?_, ?_⟩
  · have hr := regCoeff_isRegCoeff (C := model.cov) 1 (hu {0})
    rw [show (insert 0 ∅ : Finset (Fin 2)) = {0} from rfl, (isRegCoeff_singleton_iff hxx).1 hr]
    simp [Bow.cov_eq]; norm_num
  · rintro ⟨x, hx, y, hy, -, -, b, h⟩
    simp only [Set.mem_singleton_iff] at hx hy
    subst hx hy
    rcases ReflTransGen.cases_head h with h | ⟨⟨w, c⟩, hstep, -⟩
    · simp at h
    · have hA := hstep.1
      cases c <;> simp [deleteEdgeGraph, Bow.model, Bow.G] at hA
  · intro hsep
    refine hsep ⟨Sum.inl 0, Set.mem_image_of_mem _ rfl, Sum.inl 1, Set.mem_image_of_mem _ rfl,
      by simp, by simp, true, ?_⟩
    refine ReflTransGen.head (b := (Sum.inr (0, 1), false)) ?_
      (ReflTransGen.single ?_)
    · exact Digraph.bayesBall_adj_false_false.2 ⟨by simp [diagram], by simp⟩
    · exact Digraph.bayesBall_adj_true.2 ⟨by simp [diagram], by simp⟩

end BowDiagram

end LinearSEM

end CausalInference
