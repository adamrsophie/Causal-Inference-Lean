/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.PC
public import CausalInference.Discovery.PatternExamples

/-!
# The PC algorithm on small graphs

Under a d-separation oracle of the graph:

* the chain `0 → 1 → 2`: the output orients no edge, and both edges are undirected
  (`CausalInference.GraphExamples.chain_pcOutput`);
* the collider `0 → 2 ← 1`: both edges are oriented (`collider_pcOutput`);
* the graph `0 → 2 ← 1, 2 → 3`: the collider is oriented, and rule R1 orients `2 → 3`
  (`colliderTail_pcOutput`).

Without faithfulness the adjacency phase fails: with the conditional independence oracle of the
exclusive-or law, which is Markov to the collider, the edge `0 ∼ 2` of the collider is removed
(`xor_pcAdj_ne_skeleton`).
-/

@[expose] public section

namespace Digraph

variable {V : Type*} {P : Digraph V} {u v : V}

/-- An edge of the skeleton that is directed in neither direction is undirected. -/
theorem isLine_of_skeleton_adj (hs : P.skeleton.Adj u v) (h₁ : ¬ P.IsArrow u v)
    (h₂ : ¬ P.IsArrow v u) : P.IsLine u v := by
  rcases (skeleton_adj.1 hs).2 with h | h
  · by_contra hn
    exact h₁ ⟨h, fun h' => hn ⟨h, h'⟩⟩
  · by_contra hn
    exact h₂ ⟨h, fun h' => hn ⟨h', h⟩⟩

/-- Passes of the rules only remove arcs: an arc after `n + 1` passes is an arc after one. -/
theorem adj_meekPass_of_adj_iterate [Finite V] (n : ℕ)
    (h : (Digraph.meekPass^[n + 1] P).Adj u v) : (meekPass P).Adj u v := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    exact ih h.1

end Digraph

namespace CausalInference.GraphExamples

open Digraph

variable {I : Fin 3 → Fin 3 → Finset (Fin 3) → Prop} [∀ x y S, Decidable (I x y S)]

/-! ### The chain -/

/-- No edge of the chain is compelled. -/
theorem chain_not_isCompelled (u v : Fin 3) : ¬ chain.IsCompelled u v := by
  intro hc
  have hG : chain.IsAcyclic := by decide
  fin_cases u <;> fin_cases v
  all_goals first
    | exact absurd hc.1 (by decide)
    | exact (isCompelled_or_isReversible hG hc.1).2 ⟨hc, chain_isReversible_zero_one⟩
    | exact (isCompelled_or_isReversible hG hc.1).2 ⟨hc, chain_isReversible_one_two⟩

/-- **The PC algorithm on the chain.** Under a d-separation oracle of `0 → 1 → 2`, the output
directs no edge, and the edges `0 ∼ 1` and `1 ∼ 2` are undirected. -/
theorem chain_pcOutput (hI : ∀ x y S, I x y S ↔ chain.DSep {x} {y} ↑S) :
    (∀ u v, ¬ (toDigraph (pcOutput I)).IsArrow u v) ∧
      (toDigraph (pcOutput I)).IsLine 0 1 ∧ (toDigraph (pcOutput I)).IsLine 1 2 := by
  have hG : chain.IsAcyclic := by decide
  have hno : ∀ u v, ¬ (toDigraph (pcOutput I)).IsArrow u v := fun u v h =>
    chain_not_isCompelled u v (pcOutput_isCompelled hI hG h)
  have hsk := skeleton_pcOutput hI hG
  refine ⟨hno, isLine_of_skeleton_adj ?_ (hno 0 1) (hno 1 0),
    isLine_of_skeleton_adj ?_ (hno 1 2) (hno 2 1)⟩
  · rw [hsk]
    decide
  · rw [hsk]
    decide

/-! ### The collider -/

/-- **The PC algorithm on the collider.** Under a d-separation oracle of `0 → 2 ← 1`, the output
directs both edges. -/
theorem collider_pcOutput (hI : ∀ x y S, I x y S ↔ collider.DSep {x} {y} ↑S) :
    (toDigraph (pcOutput I)).IsArrow 0 2 ∧ (toDigraph (pcOutput I)).IsArrow 1 2 := by
  have hP := pcOutput_isPartialPattern hI (by decide : collider.IsAcyclic)
  exact ⟨hP.isArrow_of_isVStructure 0 2 1 (by decide),
    hP.isArrow_of_isVStructure 1 2 0 (by decide)⟩

/-! ### A collider with a tail -/

/-- **The PC algorithm on `0 → 2 ← 1, 2 → 3`.** Under a d-separation oracle of the graph, the
output directs `0 → 2` and `1 → 2` (the collider phase) and `2 → 3` (rule R1 in the first pass
of the rules). -/
theorem colliderTail_pcOutput {I : Fin 4 → Fin 4 → Finset (Fin 4) → Prop}
    [∀ x y S, Decidable (I x y S)] (hI : ∀ x y S, I x y S ↔ colliderTail.DSep {x} {y} ↑S) :
    (toDigraph (pcOutput I)).IsArrow 0 2 ∧ (toDigraph (pcOutput I)).IsArrow 1 2 ∧
      (toDigraph (pcOutput I)).IsArrow 2 3 := by
  have hG := colliderTail_isAcyclic
  have hP := pcOutput_isPartialPattern hI hG
  refine ⟨hP.isArrow_of_isVStructure 0 2 1 (by decide),
    hP.isArrow_of_isVStructure 1 2 0 (by decide), ?_⟩
  have h32 : ¬ (toDigraph (pcOutput I)).Adj 3 2 := by
    intro h
    have hn : Fintype.card (Fin 4) ^ 2 = 15 + 1 := by simp
    rw [pcOutput, toDigraph_iterate_meekPassF, toDigraph_pcColliders hI hG, hn] at h
    exact (adj_meekPass_of_adj_iterate 15 h).2 (Or.inl colliderTail_meekR1)
  have hs : (toDigraph (pcOutput I)).skeleton.Adj 2 3 := by
    rw [hP.skeleton_eq]
    decide
  exact ⟨(skeleton_adj.1 hs).2.resolve_right h32, h32⟩

/-! ### Without faithfulness -/

/-- The conditional independence oracle of the exclusive-or law. -/
def xorOracle (x y : Fin 3) (S : Finset (Fin 3)) : Prop := xorDist.CondIndep {x} {y} S

open Classical in
/-- **The PC algorithm needs faithfulness.** The exclusive-or law is Markov to the collider
`0 → 2 ← 1` (`xorDist_globalMarkov`), but with its conditional independence oracle the adjacency
phase removes the edge `0 ∼ 2`, so it does not return the skeleton of the collider. -/
theorem xor_pcAdj_ne_skeleton :
    (0, 2) ∉ pcAdj xorOracle ∧ collider.skeleton.Adj 0 2 :=
  ⟨notMem_pcAdj_of_empty xorDist_condIndep, by decide⟩

end CausalInference.GraphExamples
