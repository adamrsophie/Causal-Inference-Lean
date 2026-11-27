/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.Pattern

/-!
# Equivalence classes of small graphs

Markov equivalence is not decidable as defined (it quantifies over all sets of vertices and over
all graphs). For a fixed acyclic graph `G` with a list `E : Fin n → V × V` of its edges, every
acyclic graph with the skeleton of `G` orients each edge of `E` one way, so it is
`Digraph.orientBy E b` for a vector of bits `b`; by the characterization of Markov equivalence
(`Digraph.markovEquivalent_iff`), the Markov equivalent acyclic graphs are those
`Digraph.orientBy E b` that are acyclic and have the v-structures of `G`. This reduces the
equivalence class to a finite check, done by `decide`.

## Main results

* `Digraph.markovEquivalent_iff_orientBy`: the reduction.
* `CausalInference.GraphExamples.chain_markovEquivalent_iff`: the equivalence class of the chain
  `0 → 1 → 2` consists of the chain, the reversed chain and the fork `0 ← 1 → 2`; hence both
  edges are reversible (`chain_isReversible_zero_one`, `chain_isReversible_one_two`) and the
  pattern of the chain has no directed edge.
* `CausalInference.GraphExamples.colliderTail_markovEquivalent_iff`: the graph
  `0 → 2 ← 1, 2 → 3` is alone in its equivalence class. The edge `2 → 3` is compelled
  although it belongs to no v-structure; rule R1 orients it from the v-structure pattern
  (`colliderTail_meekR1`).
-/

@[expose] public section

namespace Digraph

variable {V : Type*} {G H : Digraph V}

/-- The graph that orients each listed pair `E i = (u, v)` as `u → v` when `b i = true` and as
`v → u` when `b i = false`. -/
def orientBy {n : ℕ} (E : Fin n → V × V) (b : Fin n → Bool) : Digraph V where
  Adj u v := ∃ i, (E i = (u, v) ∧ b i = true) ∨ (E i = (v, u) ∧ b i = false)

instance decidableRelOrientBy [DecidableEq V] {n : ℕ} (E : Fin n → V × V) (b : Fin n → Bool) :
    DecidableRel (orientBy E b).Adj :=
  fun _ _ => inferInstanceAs (Decidable (∃ _, _))

variable {n : ℕ} {E : Fin n → V × V}

/-- An acyclic graph with the skeleton of `G` orients the edges of a list `E` of the skeleton
edges of `G` one way each. -/
theorem exists_eq_orientBy
    (hE : ∀ u v, G.skeleton.Adj u v ↔ ∃ i, E i = (u, v) ∨ E i = (v, u))
    (hH : H.IsAcyclic) (hsk : H.skeleton = G.skeleton) : ∃ b, H = orientBy E b := by
  classical
  refine ⟨fun i => decide (H.Adj (E i).1 (E i).2), ?_⟩
  ext u v
  constructor
  · intro h
    have h' : G.skeleton.Adj u v := hsk ▸ skeleton_adj.2 ⟨hH.ne_of_adj h, Or.inl h⟩
    obtain ⟨i, hi | hi⟩ := (hE u v).1 h'
    · exact ⟨i, Or.inl ⟨hi, decide_eq_true (by rw [hi]; exact h)⟩⟩
    · exact ⟨i, Or.inr ⟨hi, decide_eq_false (by rw [hi]; exact hH.asymm h)⟩⟩
  · rintro ⟨i, ⟨hi, hb⟩ | ⟨hi, hb⟩⟩
    · have := of_decide_eq_true hb
      rwa [hi] at this
    · have hvu : ¬ H.Adj v u := by
        have := of_decide_eq_false hb
        rwa [hi] at this
      have h' : H.skeleton.Adj v u := hsk ▸ (hE v u).2 ⟨i, Or.inl hi⟩
      exact (skeleton_adj.1 h').2.resolve_left hvu

/-- Orienting the edges of a list of the skeleton edges of `G` gives the skeleton of `G`. -/
theorem skeleton_orientBy
    (hE : ∀ u v, G.skeleton.Adj u v ↔ ∃ i, E i = (u, v) ∨ E i = (v, u))
    (hirr : ∀ i, (E i).1 ≠ (E i).2) (b : Fin n → Bool) :
    (orientBy E b).skeleton = G.skeleton := by
  ext u v
  rw [skeleton_adj, hE]
  constructor
  · rintro ⟨-, ⟨i, ⟨hi, -⟩ | ⟨hi, -⟩⟩ | ⟨i, ⟨hi, -⟩ | ⟨hi, -⟩⟩⟩
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr hi⟩
    · exact ⟨i, Or.inr hi⟩
    · exact ⟨i, Or.inl hi⟩
  · rintro ⟨i, hi | hi⟩
    · refine ⟨fun h => hirr i (by rw [hi, h]), ?_⟩
      cases hb : b i
      · exact Or.inr ⟨i, Or.inr ⟨hi, hb⟩⟩
      · exact Or.inl ⟨i, Or.inl ⟨hi, hb⟩⟩
    · refine ⟨fun h => hirr i (by rw [hi, h]), ?_⟩
      cases hb : b i
      · exact Or.inl ⟨i, Or.inr ⟨hi, hb⟩⟩
      · exact Or.inr ⟨i, Or.inl ⟨hi, hb⟩⟩

/-- **The equivalence class as a finite check.** For a finite acyclic graph `G` and a list `E` of
its skeleton edges (each given once in some direction, without loops), an acyclic graph is Markov
equivalent to `G` if and only if it is an orientation `Digraph.orientBy E b` that is acyclic and
has the v-structures of `G`. -/
theorem markovEquivalent_iff_orientBy [Finite V] (hG : G.IsAcyclic)
    (hE : ∀ u v, G.skeleton.Adj u v ↔ ∃ i, E i = (u, v) ∨ E i = (v, u))
    (hirr : ∀ i, (E i).1 ≠ (E i).2) (hH : H.IsAcyclic) :
    MarkovEquivalent G H ↔ ∃ b, H = orientBy E b ∧ (orientBy E b).IsAcyclic ∧
      ∀ x y z, G.IsVStructure x y z ↔ (orientBy E b).IsVStructure x y z := by
  constructor
  · intro h
    obtain ⟨hsk, hv⟩ := (markovEquivalent_iff hG hH).1 h
    obtain ⟨b, rfl⟩ := exists_eq_orientBy hE hH hsk.symm
    exact ⟨b, rfl, hH, hv⟩
  · rintro ⟨b, rfl, hac, hv⟩
    exact (markovEquivalent_iff hG hac).2 ⟨(skeleton_orientBy hE hirr b).symm, hv⟩

end Digraph

namespace CausalInference.GraphExamples

open Digraph

/-! ### The chain: every edge is reversible -/

/-- The edges of the chain `0 → 1 → 2`. -/
def chainEdges : Fin 2 → Fin 3 × Fin 3 := ![(0, 1), (1, 2)]

theorem chainEdges_spec :
    ∀ u v, chain.skeleton.Adj u v ↔ ∃ i, chainEdges i = (u, v) ∨ chainEdges i = (v, u) :=
  by decide

/-- The reversed chain `0 ← 1 ← 2`. -/
abbrev chainRev : Digraph (Fin 3) := orientBy chainEdges ![false, false]

/-- The fork `0 ← 1 → 2` with center `1`. -/
abbrev forkOne : Digraph (Fin 3) := orientBy chainEdges ![false, true]

theorem chain_eq_orientBy : chain = orientBy chainEdges ![true, true] := by
  ext u v
  revert u v
  decide

/-- **The equivalence class of the chain.** An acyclic graph on three vertices is Markov
equivalent to `0 → 1 → 2` if and only if it is the chain, the reversed chain `0 ← 1 ← 2` or the
fork `0 ← 1 → 2`. The collider `0 → 1 ← 2` is excluded by its v-structure. -/
theorem chain_markovEquivalent_iff {H : Digraph (Fin 3)} (hH : H.IsAcyclic) :
    MarkovEquivalent chain H ↔ H = chain ∨ H = chainRev ∨ H = forkOne := by
  rw [markovEquivalent_iff_orientBy (by decide) chainEdges_spec (by decide) hH]
  have key : ∀ b : Fin 2 → Bool, (orientBy chainEdges b).IsAcyclic →
      (∀ x y z, chain.IsVStructure x y z ↔ (orientBy chainEdges b).IsVStructure x y z) →
      b = ![true, true] ∨ b = ![false, false] ∨ b = ![false, true] := by decide
  constructor
  · rintro ⟨b, rfl, hac, hv⟩
    rcases key b hac hv with rfl | rfl | rfl
    · exact Or.inl chain_eq_orientBy.symm
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, chain_eq_orientBy, by decide, by decide⟩
    · exact ⟨_, rfl, by decide, by decide⟩
    · exact ⟨_, rfl, by decide, by decide⟩

theorem chainRev_isAcyclic : chainRev.IsAcyclic := by decide

theorem forkOne_isAcyclic : forkOne.IsAcyclic := by decide

/-- The edge `0 → 1` of the chain is reversible: the fork `0 ← 1 → 2` is Markov equivalent. -/
theorem chain_isReversible_zero_one : chain.IsReversible 0 1 :=
  ⟨by decide, forkOne, forkOne_isAcyclic,
    (chain_markovEquivalent_iff forkOne_isAcyclic).2 (Or.inr (Or.inr rfl)), by decide⟩

/-- The edge `1 → 2` of the chain is reversible: the reversed chain is Markov equivalent. -/
theorem chain_isReversible_one_two : chain.IsReversible 1 2 :=
  ⟨by decide, chainRev, chainRev_isAcyclic,
    (chain_markovEquivalent_iff chainRev_isAcyclic).2 (Or.inr (Or.inl rfl)), by decide⟩

/-- The pattern of the chain has no directed edge: both edges are undirected. -/
theorem pattern_chain : (pattern chain).IsLine 0 1 ∧ (pattern chain).IsLine 1 2 :=
  ⟨(pattern_isLine_iff (by decide)).2 (Or.inl chain_isReversible_zero_one),
    (pattern_isLine_iff (by decide)).2 (Or.inl chain_isReversible_one_two)⟩

/-! ### A collider with a tail: an edge compelled by rule R1 -/

/-- The graph `0 → 2 ← 1, 2 → 3`. -/
def colliderTail : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3)

instance : DecidableRel colliderTail.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The edges of `colliderTail`. -/
def colliderTailEdges : Fin 3 → Fin 4 × Fin 4 := ![(0, 2), (1, 2), (2, 3)]

theorem colliderTailEdges_spec : ∀ u v, colliderTail.skeleton.Adj u v ↔
    ∃ i, colliderTailEdges i = (u, v) ∨ colliderTailEdges i = (v, u) := by
  decide

theorem colliderTail_isAcyclic : colliderTail.IsAcyclic := by decide

theorem colliderTail_eq_orientBy : colliderTail = orientBy colliderTailEdges ![true, true, true] :=
  by
  ext u v
  revert u v
  decide

/-- **The equivalence class of `0 → 2 ← 1, 2 → 3` is a singleton.** -/
theorem colliderTail_markovEquivalent_iff {H : Digraph (Fin 4)} (hH : H.IsAcyclic) :
    MarkovEquivalent colliderTail H ↔ H = colliderTail := by
  rw [markovEquivalent_iff_orientBy colliderTail_isAcyclic colliderTailEdges_spec (by decide) hH]
  have key : ∀ b : Fin 3 → Bool, (orientBy colliderTailEdges b).IsAcyclic →
      (∀ x y z, colliderTail.IsVStructure x y z ↔
        (orientBy colliderTailEdges b).IsVStructure x y z) →
      b = ![true, true, true] := by decide
  constructor
  · rintro ⟨b, rfl, hac, hv⟩
    rw [key b hac hv, colliderTail_eq_orientBy]
  · rintro rfl
    exact ⟨_, colliderTail_eq_orientBy, colliderTail_eq_orientBy ▸ colliderTail_isAcyclic,
      fun x y z => by rw [← colliderTail_eq_orientBy]⟩

/-- The edge `2 → 3` is compelled. -/
theorem colliderTail_isCompelled_two_three : colliderTail.IsCompelled 2 3 :=
  ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), fun H hH hGH => by
    rw [(colliderTail_markovEquivalent_iff hH).1 hGH]
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-- The edge `2 → 3` belongs to no v-structure, so it is undirected in the v-structure pattern. -/
theorem colliderTail_vStructurePattern_isLine : (vStructurePattern colliderTail).IsLine 2 3 := by
  decide

/-- Rule R1 orients `2 ∼ 3` in the v-structure pattern, through the directed edge `0 → 2` with
`0` and `3` nonadjacent. -/
theorem colliderTail_meekR1 : MeekR1 (vStructurePattern colliderTail) 2 3 := by
  decide

end CausalInference.GraphExamples
