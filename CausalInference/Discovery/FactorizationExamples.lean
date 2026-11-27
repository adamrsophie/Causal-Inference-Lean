/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.MarkovEquivalenceCharacterization

/-!
# Factorization does not detect Markov equivalence over one-point value types

Over value types with a single value, every law factorizes according to every graph
(`Digraph.factorizes_of_unique`). So two acyclic graphs that are not Markov equivalent, a single
edge on two vertices and the empty graph, have the same factorizing laws
(`Digraph.not_markovEquivalent_edge_bot_unit`). The observational characterization of Markov
equivalence therefore needs at least two values at every vertex.
-/

@[expose] public section

namespace Digraph

open CausalInference Finset

/-- Over value types with a single value, every law factorizes according to every graph. -/
theorem factorizes_of_unique {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*}
    [∀ v, Fintype (α v)] [∀ v, Unique (α v)] (G : Digraph V) [DecidableRel G.Adj]
    (p : FiniteDist (∀ v, α v)) : G.Factorizes p := by
  refine ⟨⟨fun _ _ _ => 1, fun _ _ _ => zero_le_one, fun _ _ => by simp⟩, fun x => ?_⟩
  have h := p.sum_eq_one
  rw [Fintype.sum_unique] at h
  simp only [MarkovKernels.factor, prod_const_one]
  rw [Subsingleton.elim x default]
  exact h

/-- The graph on two vertices with the single edge `0 → 1`. -/
def edgeZeroOne : Digraph (Fin 2) where
  Adj a b := a = 0 ∧ b = 1

instance : DecidableRel edgeZeroOne.Adj := fun a b =>
  inferInstanceAs (Decidable (a = 0 ∧ b = 1))

/-- The graph on two vertices with no edges. -/
def emptyTwo : Digraph (Fin 2) where
  Adj _ _ := False

instance : DecidableRel emptyTwo.Adj := fun _ _ => inferInstanceAs (Decidable False)

/-- **A counterexample over one-point value types.** The single edge `0 → 1` and the empty graph
on two vertices are not Markov equivalent, yet over the value type `Unit` at every vertex they
have the same factorizing laws. -/
theorem not_markovEquivalent_edge_bot_unit :
    ¬ MarkovEquivalent edgeZeroOne emptyTwo ∧
      ∀ p : FiniteDist (Fin 2 → Unit), edgeZeroOne.Factorizes p ↔ emptyTwo.Factorizes p := by
  refine ⟨fun h => ?_, fun p => ⟨fun _ => factorizes_of_unique _ p,
    fun _ => factorizes_of_unique _ p⟩⟩
  have hG : edgeZeroOne.IsAcyclic := isAcyclic_of_adj_lt id fun u v huv => by
    obtain ⟨rfl, rfl⟩ := huv
    decide
  have hH : emptyTwo.IsAcyclic := isAcyclic_of_adj_lt id fun _ _ huv => huv.elim
  have hsk := ((markovEquivalent_iff hG hH).1 h).1
  have h01 : edgeZeroOne.skeleton.Adj 0 1 := skeleton_adj.2 ⟨by decide, Or.inl ⟨rfl, rfl⟩⟩
  rw [hsk, skeleton_adj] at h01
  exact h01.2.elim id id

end Digraph
