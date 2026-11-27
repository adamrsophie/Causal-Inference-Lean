/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.DSeparationExamples

/-!
# The Markov blanket

## Main definitions

* `Digraph.coparents G v`: the other parents of the children of `v` (Pearl's spouses), that is,
  the vertices `u ≠ v` with a common child with `v`.
* `Digraph.markovBlanket G v`: the parents, the children, and the co-parents of `v`.
* `Digraph.markovBlanketFinset G v`: its finite version.

## Main results

* `Digraph.dSep_markovBlanket`: the Markov blanket of `v` d-separates `v` from every vertex
  outside the blanket and different from `v`. No acyclicity is needed for this graph statement.
* `Digraph.IsAcyclic.notMem_markovBlanket`: in an acyclic graph `v` is not in its own blanket,
  so the theorem is not vacuous there (an endpoint in the conditioning set would be blocked
  trivially).
* `Digraph.IsAcyclic.markovBlanket_subset_of_dSep`: minimality. In an acyclic graph, every set
  `S` that omits `v` and d-separates `v` from the vertices outside `S` contains the blanket;
  `Digraph.markovBlanket_subset_insert_of_dSep` is the version without acyclicity.
* Examples by `decide`.

## References

* J. Pearl (1988), *Probabilistic Reasoning in Intelligent Systems*, section 3.3.
* J. Pearl, M. Glymour, N. P. Jewell (2016), *Causal Inference in Statistics: A Primer*,
  study question 2.4.1 (d).
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- The co-parents (spouses) of `v`: the vertices `u ≠ v` that share a child with `v`. -/
def coparents (G : Digraph V) (v : V) : Set V := {u | u ≠ v ∧ ∃ w, G.Adj v w ∧ G.Adj u w}

/-- The Markov blanket of `v`: its parents, its children, and the other parents of its
children. -/
def markovBlanket (G : Digraph V) (v : V) : Set V :=
  G.parents v ∪ G.children v ∪ G.coparents v

variable {G : Digraph V} {u v : V}

theorem mem_markovBlanket :
    u ∈ G.markovBlanket v ↔ G.Adj u v ∨ G.Adj v u ∨ (u ≠ v ∧ ∃ w, G.Adj v w ∧ G.Adj u w) := by
  simp [markovBlanket, coparents, or_assoc]

/-- In an acyclic graph a vertex is not in its own Markov blanket. -/
theorem IsAcyclic.notMem_markovBlanket (hG : G.IsAcyclic) (v : V) : v ∉ G.markovBlanket v := by
  rw [mem_markovBlanket]
  rintro (h | h | ⟨h, -⟩)
  · exact hG.irrefl v h
  · exact hG.irrefl v h
  · exact h rfl

/-- The Markov blanket of `v` d-separates `v` from every vertex outside the blanket and
different from `v`. -/
theorem dSep_markovBlanket (G : Digraph V) (v : V) :
    G.DSep {v} (insert v (G.markovBlanket v))ᶜ (G.markovBlanket v) := by
  set M := G.markovBlanket v
  have inv : ∀ s : V × Bool, ReflTransGen (G.bayesBall M).Adj (v, false) s →
      s = (v, false) ∨ (s.1 ∈ M ∧ (s.2 = true → G.Adj v s.1)) := by
    intro s hs
    induction hs with
    | refl => exact Or.inl rfl
    | @tail t₁ t₂ _ h₁₂ ih =>
      obtain ⟨x, f⟩ := t₁
      obtain ⟨w, c⟩ := t₂
      rcases ih with h | ⟨hx, hxv⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        cases c
        · exact Or.inr ⟨Or.inl (Or.inl (bayesBall_adj_false_false.1 h₁₂).1),
            fun h => Bool.noConfusion h⟩
        · have hvw := (bayesBall_adj_true.1 h₁₂).1
          exact Or.inr ⟨Or.inl (Or.inr hvw), fun _ => hvw⟩
      · cases c
        · cases f
          · exact absurd hx (bayesBall_adj_false_false.1 h₁₂).2
          · have hwx := (bayesBall_adj_true_false.1 h₁₂).1
            have hvx := hxv rfl
            by_cases hwv : w = v
            · exact Or.inl (by rw [hwv])
            · exact Or.inr ⟨Or.inr ⟨hwv, x, hvx, hwx⟩,
                fun h => Bool.noConfusion h⟩
        · exact absurd hx (bayesBall_adj_true.1 h₁₂).2
  rintro ⟨x, rfl, y, hy, -, hyM, b, hxy⟩
  rcases inv _ hxy with h | ⟨h, -⟩
  · obtain ⟨rfl, -⟩ := Prod.mk.inj h
    exact hy (Set.mem_insert _ _)
  · exact hyM h

/-- Minimality of the Markov blanket. If `v ∉ S` and `S` d-separates `v` from every vertex
outside `S` and different from `v`, then every member of the blanket of `v` other than `v`
lies in `S`. A parent or child outside `S` would be adjacent to `v`; a co-parent `u` outside `S`
with a common child `w` would be d-connected to `v` through the collider `v → w ← u`, since
`w` is a child and so lies in `S`. No acyclicity is needed. -/
theorem markovBlanket_subset_insert_of_dSep {S : Set V} (hvS : v ∉ S)
    (h : G.DSep {v} (insert v S)ᶜ S) : G.markovBlanket v ⊆ insert v S := by
  have key : ∀ u, u ∉ insert v S → ¬ G.DConn {v} {u} S := fun u hu hc =>
    h (hc.mono_right (Set.singleton_subset_iff.2 hu))
  have notS : ∀ {u}, u ∉ insert v S → u ∉ S := fun hu hs => hu (Set.mem_insert_of_mem _ hs)
  have child : ∀ w, G.Adj v w → w ∈ insert v S := fun w hw => by
    by_contra hw'
    exact key w hw' (dConn_of_adj hw hvS (notS hw'))
  intro u hu
  by_contra hu'
  rw [mem_markovBlanket] at hu
  rcases hu with huv | hvu | ⟨-, w, hvw, huw⟩
  · exact key u hu' (dConn_of_adj huv (notS hu') hvS).symm
  · exact hu' (child u hvu)
  · rcases child w hvw with rfl | hwS
    · exact key u hu' (dConn_of_adj huw (notS hu') hvS).symm
    · exact key u hu' (dConn_of_collider hvw huw hvS ⟨w, hwS, .refl⟩ (notS hu'))

/-- Minimality of the Markov blanket in an acyclic graph (Primer, study question 2.4.1 (d)): if
`v ∉ S` and `S` d-separates `v` from every vertex outside `S` and different from `v`, then the
blanket of `v` is contained in `S`. Together with `dSep_markovBlanket`, the blanket is the
smallest such set. -/
theorem IsAcyclic.markovBlanket_subset_of_dSep (hG : G.IsAcyclic) {S : Set V} (hvS : v ∉ S)
    (h : G.DSep {v} (insert v S)ᶜ S) : G.markovBlanket v ⊆ S := fun u hu => by
  rcases markovBlanket_subset_insert_of_dSep hvS h hu with rfl | huS
  · exact absurd hu (hG.notMem_markovBlanket u)
  · exact huS

section Finset

variable (G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The Markov blanket as a finset, for a finite vertex type with decidable adjacency. -/
def markovBlanketFinset (v : V) : Finset V :=
  Finset.univ.filter fun u => G.Adj u v ∨ G.Adj v u ∨ (u ≠ v ∧ ∃ w, G.Adj v w ∧ G.Adj u w)

variable {G}

@[simp] theorem mem_markovBlanketFinset :
    u ∈ G.markovBlanketFinset v ↔ u ∈ G.markovBlanket v := by
  simp [markovBlanketFinset, mem_markovBlanket]

@[simp, norm_cast] theorem coe_markovBlanketFinset (v : V) :
    (G.markovBlanketFinset v : Set V) = G.markovBlanket v := by
  ext; simp

instance decidableMemMarkovBlanket (v : V) : DecidablePred (· ∈ G.markovBlanket v) :=
  fun _ => decidable_of_iff _ mem_markovBlanketFinset

end Finset

end Digraph

namespace CausalInference.MarkovBlanketExamples

open DSeparationExamples

-- In the six-vertex graph (`0 → 1`, `2 → 1`, `1 → 3`, `3 → 4`, `2 → 5`, `5 → 4`, `0 → 5`), the
-- blanket of `1` is its parents `0`, `2` and its child `3`; the blanket of `5` adds the
-- co-parent `3` of its child `4`.
example : six.markovBlanketFinset 1 = {0, 2, 3} := by decide +kernel
example : six.markovBlanketFinset 5 = {0, 2, 3, 4} := by decide +kernel
example : six.DSep {5} {1} (six.markovBlanket 5) := by decide +kernel
-- The co-parent is needed: without `3`, conditioning on the child `4` connects `5` and `1`.
example : ¬ six.DSep {5} {1} {0, 2, 4} := by decide +kernel

end CausalInference.MarkovBlanketExamples
