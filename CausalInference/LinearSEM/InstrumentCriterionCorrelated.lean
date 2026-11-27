/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.CorrelatedErrors
public import CausalInference.LinearSEM.InstrumentCriterion

/-!
# The instrument criterion with correlated errors

The graphical instrument criterion for linear models whose errors are correlated along the
bidirected edges of a path diagram (`LinearSEM.PathDiagram`, errors given by latent common
causes). Separation in a mixed graph is m-separation (`ADMG.MSep`), and the graph with the
edges into the treatment `x` removed is `ADMG.deleteIncoming`, which also removes every
bidirected edge at `x` (Pearl's graph with a bar over `x`).

## Main results

* `ADMG.mSep_deleteOutgoing_of_mSep_deleteIncoming`: if `x` is not among the covariates `S`,
  m-separation of `z` and `y` (both different from `x`) by `S` in the graph with the edges into
  `x` removed implies m-separation in the graph with the directed edges out of `x` removed.
* `LinearSEM.PathDiagram.partialCov_eq_T_mul_partialCov_of_mSep`: let `z` and the covariates
  `S` be nondescendants of `x` in the diagram, let `y ≠ x`, let the covariance block of `S` be
  invertible, and let `S` m-separate `z` from `y` in the diagram with the edges into `x`
  removed. Then `Σ_{zy·S} = T y x Σ_{zx·S}`.
* `LinearSEM.PathDiagram.cov_eq_T_mul_cov_of_mSep`: the unconditional form
  `Σ z y = T y x Σ z x`.
* `LinearSEM.CorrelatedInstrumentModel.counterexample`: on `Z → X → Y` with `Z ↔ Y` the moment
  condition fails, while `Z` is a nondescendant of `X`, `Y ≠ X`, and the directed part alone
  d-separates `Z` from `Y` once the edges into `X` are removed.

## Notes

The bidirected edges that matter are those that m-connect `z` and `y` after the edges into
`x` are cut: `z ↔ y`, or `z ↔ w` with `w` an ancestor of `y` there. A bidirected edge `z ↔ x`
or `x ↔ y` does not spoil the criterion, since every bidirected edge at `x` is removed. The
result covers the error covariances with a representation along the bidirected edges by
latent factors (`LinearSEM.PathDiagram`), as the m-separation bridge
`LinearSEM.PathDiagram.partialCov_eq_zero_of_mSep` does.

## References

* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, sections 5.3
  and 7.4.5.
-/

@[expose] public section

namespace CausalInference

open Relation

namespace ADMG

variable {V : Type*} {G : ADMG V} {x : V} {S : Set V}

/-- The vertices of the canonical DAG that the removal of the edges into `x` keeps connected:
the observed vertices other than `x` and the latent vertices of pairs avoiding `x`. -/
def AvoidsVertex (x : V) : V ⊕ V × V → Prop
  | .inl v => v ≠ x
  | .inr p => p.1 ≠ x ∧ p.2 ≠ x

theorem not_adj_inl_deleteOutgoing (t : V ⊕ V × V) :
    ¬ (G.deleteOutgoing {x}).canonicalDAG.Adj (.inl x) t := by
  rcases t with v | p
  · exact fun h => h.2 rfl
  · exact not_canonicalDAG_adj_inr

theorem eq_of_reflTransGen_inl_deleteOutgoing {t : V ⊕ V × V}
    (h : ReflTransGen (G.deleteOutgoing {x}).canonicalDAG.Adj (.inl x) t) : t = .inl x := by
  rcases ReflTransGen.cases_head h with h | ⟨c, hc, -⟩
  · exact h.symm
  · exact absurd hc (not_adj_inl_deleteOutgoing c)

theorem avoidsVertex_of_adj {a c : V ⊕ V × V} (h : (G.deleteOutgoing {x}).canonicalDAG.Adj a c)
    (hc : c ≠ .inl x) : AvoidsVertex x c := by
  rcases c with v | p
  · exact fun e => hc (e ▸ rfl)
  · exact absurd h not_canonicalDAG_adj_inr

/-- An edge between two vertices that avoid `x` survives the removal of the edges into `x`. -/
theorem adj_deleteIncoming_of_adj {a b : V ⊕ V × V}
    (h : (G.deleteOutgoing {x}).canonicalDAG.Adj a b) (ha : AvoidsVertex x a)
    (hb : AvoidsVertex x b) : (G.deleteIncoming {x}).canonicalDAG.Adj a b := by
  rcases a with u | p <;> rcases b with v | q
  · exact ⟨h.1, hb⟩
  · exact absurd h not_canonicalDAG_adj_inr
  · exact ⟨⟨h.1, ha.1, ha.2⟩, h.2⟩
  · exact absurd h not_canonicalDAG_adj_inr

/-- A directed path that ends at an observed vertex other than `x` and starts at a vertex
avoiding `x` survives the removal of the edges into `x`. -/
theorem reflTransGen_deleteIncoming_of_reflTransGen {a b : V ⊕ V × V}
    (h : ReflTransGen (G.deleteOutgoing {x}).canonicalDAG.Adj a b) (hb : b ≠ .inl x) :
    AvoidsVertex x a → ReflTransGen (G.deleteIncoming {x}).canonicalDAG.Adj a b := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact fun _ => .refl
  | @head a c hac hcb ih =>
    intro ha
    have hc : c ≠ .inl x := by
      rintro rfl
      exact hb (eq_of_reflTransGen_inl_deleteOutgoing hcb)
    have hc' := avoidsVertex_of_adj hac hc
    exact .head (adj_deleteIncoming_of_adj hac ha hc') (ih hc')

theorem mem_ancestorsOf_deleteIncoming (hSx : x ∉ S) {t : V ⊕ V × V}
    (ht : t ∈ (G.deleteOutgoing {x}).canonicalDAG.ancestorsOf (Sum.inl '' S))
    (hta : AvoidsVertex x t) :
    t ∈ (G.deleteIncoming {x}).canonicalDAG.ancestorsOf (Sum.inl '' S) := by
  obtain ⟨s', ⟨s, hs, rfl⟩, hts⟩ := ht
  refine ⟨_, ⟨s, hs, rfl⟩, reflTransGen_deleteIncoming_of_reflTransGen hts ?_ hta⟩
  rintro ⟨⟩
  exact hSx hs

theorem not_mem_ancestorsOf_inl (hSx : x ∉ S) :
    Sum.inl x ∉ (G.deleteOutgoing {x}).canonicalDAG.ancestorsOf (Sum.inl '' S) := by
  rintro ⟨s', ⟨s, hs, rfl⟩, h⟩
  cases eq_of_reflTransGen_inl_deleteOutgoing h
  exact hSx hs

theorem head_mem_of_activeTrail {H : Digraph (V ⊕ V × V)} {Z : Set (V ⊕ V × V)} {a : Bool}
    {u w : V ⊕ V × V} {l : List (V ⊕ V × V)} (p : H.ActiveTrail Z a u w l) : u ∈ l := by
  cases p <;> simp

/-- With the directed edges out of `x` removed, an active trail that reaches `x` along an
arrowhead cannot continue to an endpoint avoiding `x`. -/
theorem false_of_activeTrail_inl (hSx : x ∉ S) {w : V ⊕ V × V} {l : List (V ⊕ V × V)}
    (q : (G.deleteOutgoing {x}).canonicalDAG.ActiveTrail (Sum.inl '' S) true (.inl x) w l)
    (hw : AvoidsVertex x w) : False := by
  cases q with
  | nil _ => exact hw rfl
  | fwd h _ _ => exact not_adj_inl_deleteOutgoing _ h
  | collider _ hc _ => exact not_mem_ancestorsOf_inl hSx hc

/-- On a simple active trail, the vertex entered against an edge into a vertex `u` avoiding `x`
also avoids `x`. A latent vertex of a pair containing `x` would have to be left toward `x`. -/
theorem avoidsVertex_of_adj_activeTrail (hSx : x ∉ S) {u v w : V ⊕ V × V}
    {l : List (V ⊕ V × V)} (h : (G.deleteOutgoing {x}).canonicalDAG.Adj v u)
    (hu : AvoidsVertex x u)
    (q : (G.deleteOutgoing {x}).canonicalDAG.ActiveTrail (Sum.inl '' S) false v w l)
    (hl : (u :: l).Nodup) (hw : AvoidsVertex x w) : AvoidsVertex x v := by
  rcases v with v | ⟨p1, p2⟩
  · rintro rfl
    exact not_adj_inl_deleteOutgoing _ h
  rcases u with u | q'
  swap
  · exact absurd h not_canonicalDAG_adj_inr
  obtain ⟨-, hu'⟩ := h
  cases q with
  | nil _ => exact hw
  | bwd h' _ _ => exact absurd h' not_canonicalDAG_adj_inr
  | @fwd _ _ v' _ l'' h' _ q'' =>
    rcases v' with b | r
    swap
    · exact absurd h' not_canonicalDAG_adj_inr
    obtain ⟨-, hb⟩ := h'
    by_cases hbx : b = x
    · subst hbx
      exact (false_of_activeTrail_inl hSx q'' hw).elim
    have hbu : b ≠ u := by
      rintro rfl
      exact (List.nodup_cons.1 hl).1 (List.mem_cons_of_mem _ (head_mem_of_activeTrail q''))
    change u ≠ x at hu
    change p1 ≠ x ∧ p2 ≠ x
    simp only at hu' hb
    rcases hu' with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hbu
    · exact ⟨hu, hbx⟩
    · exact ⟨hbx, hu⟩
    · exact absurd rfl hbu

/-- A simple active trail of the canonical DAG of `G` with the directed edges out of `x`
removed, between vertices avoiding `x`, is an active trail of the canonical DAG of `G` with the
edges into `x` removed, when `x` is not conditioned on. -/
theorem activeTrail_deleteIncoming (hSx : x ∉ S) {a : Bool} {u w : V ⊕ V × V}
    {l : List (V ⊕ V × V)}
    (p : (G.deleteOutgoing {x}).canonicalDAG.ActiveTrail (Sum.inl '' S) a u w l)
    (hl : l.Nodup) (hu : AvoidsVertex x u) (hw : AvoidsVertex x w) :
    (G.deleteIncoming {x}).canonicalDAG.ActiveTrail (Sum.inl '' S) a u w l := by
  induction p with
  | nil hv => exact .nil hv
  | @fwd _ u v _ _ h hu' q ih =>
    have hv : AvoidsVertex x v := avoidsVertex_of_adj h fun e => by
      subst e
      exact false_of_activeTrail_inl hSx q hw
    exact .fwd (adj_deleteIncoming_of_adj h hu hv) hu' (ih hl.of_cons hv hw)
  | bwd h hu' q ih =>
    have hv := avoidsVertex_of_adj_activeTrail hSx h hu q hl hw
    exact .bwd (adj_deleteIncoming_of_adj h hv hu) hu' (ih hl.of_cons hv hw)
  | collider h hc q ih =>
    have hv := avoidsVertex_of_adj_activeTrail hSx h hu q hl hw
    exact .collider (adj_deleteIncoming_of_adj h hv hu) (mem_ancestorsOf_deleteIncoming hSx hc hu)
      (ih hl.of_cons hv hw)

/-- If `x` is not among the covariates `S`, m-separation of `z` and `y` (both different from
`x`) by `S` in the graph with the edges into `x` removed (directed edges into `x` and
bidirected edges at `x`) implies m-separation in the graph with the directed edges out of `x`
removed. -/
theorem mSep_deleteOutgoing_of_mSep_deleteIncoming {z y : V} (hSx : x ∉ S) (hz : z ≠ x)
    (hy : y ≠ x) (h : (G.deleteIncoming {x}).MSep {z} {y} S) :
    (G.deleteOutgoing {x}).MSep {z} {y} S := by
  intro hc
  obtain ⟨a, ha, b, hb, l, hl, hnd⟩ := Digraph.dConn_iff_dConnPath.1 hc
  obtain ⟨z', hz', rfl⟩ := ha
  obtain ⟨y', hy', rfl⟩ := hb
  rw [Set.mem_singleton_iff] at hz' hy'
  subst hz' hy'
  exact h (Digraph.dConn_iff_dConnPath.2 ⟨_, ⟨z', rfl, rfl⟩, _, ⟨y', rfl, rfl⟩, l,
    activeTrail_deleteIncoming hSx hl hnd hz hy, hnd⟩)

end ADMG

namespace LinearSEM

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace PathDiagram

variable {M : LinearSEM V} (F : M.PathDiagram)

/-- **The instrument criterion with correlated errors, conditional form.** Let `z` and the
covariates `S` be nondescendants of `x` in the diagram, let `y ≠ x`, let the covariance block of
`S` be invertible, and let `S` m-separate `z` from `y` in the diagram with the edges into `x`
removed. Then the partial covariances given `S` satisfy `Σ_{zy·S} = T y x Σ_{zx·S}`. -/
theorem partialCov_eq_T_mul_partialCov_of_mSep {x y z : V} {S : Finset V}
    (hz : z ∉ F.G.directed.descendantsOf {x})
    (hS : ∀ s ∈ S, s ∉ F.G.directed.descendantsOf {x}) (hy : y ≠ x)
    (hsep : (F.G.deleteIncoming {x}).MSep {z} {y} ↑S) (hu : IsUnit (subCov M.cov S)) :
    partialCov M.cov S z y = M.T y x * partialCov M.cov S z x := by
  set M₀ := F.toModel
  have hzx : z ≠ x := fun h => hz ⟨x, rfl, h ▸ ReflTransGen.refl⟩
  have hSx : x ∉ (S : Set V) := fun h => hS x h ⟨x, rfl, ReflTransGen.refl⟩
  let F' := F.transfer (M' := M₀.cutOutgoing x) _ F.acyclic.deleteOutgoing
    (M₀.cutOutgoing x).B_support rfl
  have h0 : partialCov (M₀.cutOutgoing x).cov S z y = 0 :=
    F'.partialCov_eq_zero_of_mSep (ADMG.mSep_deleteOutgoing_of_mSep_deleteIncoming hSx hzx hy hsep)
      (M₀.isUnit_subCov_cutOutgoing hS hu)
  exact M₀.partialCov_eq_T_mul_partialCov_of_cutOutgoing hz hS hy hu h0

/-- **The instrument criterion with correlated errors.** If `z` is a nondescendant of `x` in
the diagram, `y ≠ x`, and `z` and `y` are m-separated in the diagram with the edges into `x`
removed, then `Σ z y = T y x Σ z x`. -/
theorem cov_eq_T_mul_cov_of_mSep {x y z : V} (hz : z ∉ F.G.directed.descendantsOf {x})
    (hy : y ≠ x) (hsep : (F.G.deleteIncoming {x}).MSep {z} {y} ∅) :
    M.cov z y = M.T y x * M.cov z x := by
  have h := F.partialCov_eq_T_mul_partialCov_of_mSep (S := ∅) hz (fun _ hs => by simp at hs) hy
    (by simpa using hsep) (isUnit_subCov_empty _)
  rwa [partialCov_empty, partialCov_empty] at h

end PathDiagram

/-! ### A correlated instrument -/

namespace CorrelatedInstrumentModel

open Matrix Criteria

/-- The graph `Z → X → Y` on `Fin 3` (`X = 0`, `Z = 1`, `Y = 2`). -/
abbrev graph : Digraph (Fin 3) := ofEdges [(1, 0), (0, 2)]

/-- One latent factor `ℓ (1, 2)` loading `1` on the errors of `Z` and `Y`. -/
def Λ : Matrix (Fin 3) (Fin 3 × Fin 3) ℝ := fun v p => if p = (1, 2) ∧ (v = 1 ∨ v = 2) then 1 else 0

/-- The residual variances: `1` for `X`, `0` for `Z` and `Y`. -/
def D : Fin 3 → ℝ := ![1, 0, 0]

/-- The error covariance: unit variances and `Cov(ε_Z, ε_Y) = 1`. -/
def errCov : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 1; 0, 1, 1]

theorem errCov_eq : errCov = Λ * Λᵀ + diagonal D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [errCov, Λ, D, Matrix.mul_apply]

theorem psd : errCov.PosSemidef := by
  rw [errCov_eq]
  have h := Matrix.posSemidef_self_mul_conjTranspose Λ
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact h.add (PosSemidef.diagonal fun i => by fin_cases i <;> simp [D])

/-- The model `X = Z + ε_X`, `Z = ε_Z`, `Y = X + ε_Y` with `Cov(ε_Z, ε_Y) = 1`. -/
def model : LinearSEM (Fin 3) where
  G := graph
  acyclic := by decide +kernel
  B := !![0, 1, 0; 0, 0, 0; 1, 0, 0]
  B_support v u h := by
    fin_cases v <;> fin_cases u <;> simp_all [graph, ofEdges]
  Ω := errCov
  Ω_posSemidef := psd

/-- The path diagram of `model`: `Z → X → Y` and `Z ↔ Y`. -/
def diagram : model.PathDiagram where
  G := ⟨graph, SimpleGraph.fromEdgeSet {s(1, 2)}⟩
  acyclic := model.acyclic
  B_support := model.B_support
  Λ := Λ
  Λ_support v p h := by
    have hp : p = (1, 2) ∧ (v = 1 ∨ v = 2) := by
      by_contra hp
      exact h (by simp [Λ, hp])
    obtain ⟨rfl, hv⟩ := hp
    exact ⟨by simp, hv⟩
  D := D
  D_nonneg i := by fin_cases i <;> simp [D]
  Ω_eq := errCov_eq

theorem T_eq : model.T = !![1, 1, 0; 0, 1, 0; 1, 1, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_three]

/-- **A correlated instrument breaks the moment condition.** In `model` the instrument `Z` is a
nondescendant of `X`, `Y ≠ X`, and the directed part alone d-separates `Z` from `Y` once the
edges into `X` are removed; but the errors of `Z` and `Y` are correlated along `Z ↔ Y`. The
covariances are `Σ z y = 2` and `Σ z x = 1` with total effect `T y x = 1`, so
`Σ z y ≠ T y x Σ z x`, and hence `Z` and `Y` are m-connected in the diagram with the edges into
`X` removed. -/
theorem counterexample :
    (1 : Fin 3) ∉ model.G.descendantsOf {0} ∧ (2 : Fin 3) ≠ 0 ∧
      (model.G.deleteIncoming {0}).DSep {1} {2} ∅ ∧ diagram.G.bidirected.Adj 1 2 ∧
      model.Ω 1 2 ≠ 0 ∧ model.cov 1 2 = 2 ∧ model.cov 1 0 = 1 ∧ model.T 2 0 = 1 ∧
      model.cov 1 2 ≠ model.T 2 0 * model.cov 1 0 ∧
      ¬ (diagram.G.deleteIncoming {0}).MSep {1} {2} ∅ := by
  have hz : (1 : Fin 3) ∉ graph.descendantsOf {0} := by decide +kernel
  have h12 : model.cov 1 2 = 2 := by
    rw [cov_apply, T_eq]; simp [model, errCov, Fin.sum_univ_three]; norm_num
  have h10 : model.cov 1 0 = 1 := by
    rw [cov_apply, T_eq]; simp [model, errCov, Fin.sum_univ_three]
  have hT : model.T 2 0 = 1 := by rw [T_eq]; simp
  have hne : model.cov 1 2 ≠ model.T 2 0 * model.cov 1 0 := by
    rw [h12, h10, hT]; norm_num
  refine ⟨hz, by decide, (by decide +kernel : (graph.deleteIncoming {0}).DSep {1} {2} ∅),
    by simp [diagram], by simp [model, errCov], h12, h10, hT, hne, fun h => hne ?_⟩
  exact diagram.cov_eq_T_mul_cov_of_mSep hz (by decide) h

end CorrelatedInstrumentModel

end LinearSEM

end CausalInference
