/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.CoveredEdge

/-!
# The characterization of Markov equivalence

**Theorem** (Verma and Pearl 1990; Pearl 2009, *Causality*, 2nd edition, Theorem 1.2.8). Two
acyclic directed graphs on the same finite vertex type are Markov equivalent (have the same
d-separation relation) if and only if they have the same skeleton and the same v-structures.

The "only if" half is `Digraph.MarkovEquivalent.skeleton_eq` and
`Digraph.MarkovEquivalent.isVStructure_iff`. The "if" half follows the transformational proof of
Chickering (1995): if two acyclic graphs with the same skeleton and the same v-structures differ,
some edge of the first graph that is reversed in the second is covered
(`Digraph.exists_isCovered_of_skeleton_eq`); reversing it keeps the skeleton and the
v-structures, preserves d-separation (`Digraph.IsCovered.dSep_reverseEdge_iff`) and reduces the
number of edges on which the two graphs disagree. So one graph is reached from the other by a
sequence of covered edge reversals.

## Main definitions

* `Digraph.CoveredReversal G G'`: `G` is acyclic and `G'` is obtained from `G` by reversing one
  covered edge.

## Main results

* `Digraph.exists_isCovered_of_skeleton_eq`: the transformational step.
* `Digraph.reflTransGen_coveredReversal`: graphs with the same skeleton and v-structures are
  joined by a sequence of covered edge reversals.
* `Digraph.markovEquivalent_iff`: **the characterization of Markov equivalence**.
* `Digraph.markovEquivalent_iff_reflTransGen_coveredReversal`: the transformational
  characterization (Chickering 1995).
* `Digraph.markovEquivalent_iff_forall_factorizes`: Markov equivalence is observational
  equivalence in the sense of Pearl (2009): the same distributions over binary variables
  factorize according to both graphs; `Digraph.MarkovEquivalent.factorizes_iff` gives the
  forward direction for arbitrary finite value types.

## References

* T. Verma and J. Pearl (1990), *Equivalence and synthesis of causal models*.
* D. M. Chickering (1995), *A transformational characterization of equivalent Bayesian network
  structures*.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, Theorem 1.2.8.
-/

@[expose] public section

namespace Digraph

open Relation Finset CausalInference

variable {V : Type*} {G H : Digraph V} {u v : V}

/-- One step of the transformational characterization: `G` is acyclic and `G'` is `G` with one
covered edge reversed. -/
def CoveredReversal (G G' : Digraph V) : Prop :=
  G.IsAcyclic ∧ ∃ x y, G.IsCovered x y ∧ G' = G.reverseEdge x y

/-! ### Graphs with the same skeleton -/

/-- If two acyclic graphs have the same skeleton, an edge of the first that is missing from the
second is reversed in the second. -/
theorem adj_swap_of_skeleton_eq (hsk : G.skeleton = H.skeleton) (hG : G.IsAcyclic)
    (h : G.Adj u v) (hn : ¬ H.Adj u v) : H.Adj v u := by
  have h' : H.skeleton.Adj u v := hsk ▸ skeleton_adj.2 ⟨hG.ne_of_adj h, Or.inl h⟩
  exact (skeleton_adj.1 h').2.resolve_left hn

/-- Two acyclic graphs with the same skeleton are equal as soon as every edge of the first is an
edge of the second. -/
theorem eq_of_skeleton_eq (hsk : G.skeleton = H.skeleton) (hH : H.IsAcyclic)
    (h : ∀ u v, G.Adj u v → H.Adj u v) : G = H := by
  ext u v
  refine ⟨h u v, fun huv => ?_⟩
  have h' : G.skeleton.Adj u v := hsk.symm ▸ skeleton_adj.2 ⟨hH.ne_of_adj huv, Or.inl huv⟩
  rcases (skeleton_adj.1 h').2 with h'' | h''
  · exact h''
  · exact absurd (h v u h'') (hH.asymm huv)

/-- Acyclic graphs with the same skeleton have the same nonadjacent pairs, in edge form. -/
theorem not_adj_of_skeleton_eq (hsk : G.skeleton = H.skeleton) (hne : u ≠ v)
    (hn : ¬ G.Adj u v) (hn' : ¬ G.Adj v u) : ¬ H.Adj u v := fun h => by
  have h' : G.skeleton.Adj u v := hsk ▸ skeleton_adj.2 ⟨hne, Or.inl h⟩
  rcases (skeleton_adj.1 h').2 with h'' | h''
  · exact hn h''
  · exact hn' h''

/-! ### The transformational step -/

/-- **The transformational step** (Chickering 1995). Let `G` and `H` be acyclic graphs on a finite
vertex type with the same skeleton and the same v-structures, and suppose some edge of `G` is
reversed in `H`. Then some edge `x → y` of `G` that is reversed in `H` is covered in `G`. Take,
with a topological order of `G`, the lowest head `y` of a reversed edge and then the highest tail
`x` of a reversed edge into `y`. -/
theorem exists_isCovered_of_skeleton_eq [Finite V] (hG : G.IsAcyclic) (hH : H.IsAcyclic)
    (hsk : G.skeleton = H.skeleton)
    (hv : ∀ a c b, G.IsVStructure a c b ↔ H.IsVStructure a c b)
    (hne : ∃ u v, G.Adj u v ∧ H.Adj v u) : ∃ x y, G.IsCovered x y ∧ H.Adj y x := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  set S₁ : Finset V := univ.filter fun y => ∃ x, G.Adj x y ∧ H.Adj y x
  have hS₁ : S₁.Nonempty := by
    obtain ⟨u, v, h⟩ := hne
    exact ⟨v, mem_filter.2 ⟨mem_univ v, u, h⟩⟩
  obtain ⟨y, hyS, hymin⟩ := S₁.exists_min_image f hS₁
  set S₂ : Finset V := univ.filter fun x => G.Adj x y ∧ H.Adj y x
  have hS₂ : S₂.Nonempty := by
    obtain ⟨x, h⟩ := (mem_filter.1 hyS).2
    exact ⟨x, mem_filter.2 ⟨mem_univ x, h⟩⟩
  obtain ⟨x, hxS, hxmax⟩ := S₂.exists_max_image f hS₂
  obtain ⟨hxy, hyx⟩ := (mem_filter.1 hxS).2
  have hmin : ∀ y' x', G.Adj x' y' → H.Adj y' x' → f y ≤ f y' := fun y' x' h₁ h₂ =>
    hymin y' (mem_filter.2 ⟨mem_univ _, x', h₁, h₂⟩)
  have hmax : ∀ x', G.Adj x' y → H.Adj y x' → f x' ≤ f x := fun x' h₁ h₂ =>
    hxmax x' (mem_filter.2 ⟨mem_univ _, h₁, h₂⟩)
  have hfxy := hf hxy
  have h₁ : ∀ z, G.Adj z x → G.Adj z y := by
    intro z hzx
    have hfz := hf hzx
    have hHzx : H.Adj z x := by
      by_contra hn
      have := hmin x z hzx (adj_swap_of_skeleton_eq hsk hG hzx hn)
      omega
    by_contra hzy
    have hyz : ¬ G.Adj y z := fun h => by have := hf h; omega
    have hzy' : z ≠ y := fun h => by subst h; omega
    have hvs : H.IsVStructure z x y := ⟨hHzx, hyx, hzy',
      not_adj_of_skeleton_eq hsk hzy' hzy hyz, not_adj_of_skeleton_eq hsk hzy'.symm hyz hzy⟩
    exact hG.asymm hxy ((hv z x y).2 hvs).2.1
  have h₂ : ∀ z, G.Adj z y → z ≠ x → G.Adj z x := by
    intro z hzy hzx
    have hfz := hf hzy
    by_cases hadj : G.Adj z x ∨ G.Adj x z
    · rcases hadj with h | hxz
      · exact h
      · exfalso
        have hfxz := hf hxz
        have hHzy : H.Adj z y := by
          by_contra hn
          have := hmax z hzy (adj_swap_of_skeleton_eq hsk hG hzy hn)
          omega
        have hHxz : H.Adj x z := by
          by_contra hn
          have := hmin z x hxz (adj_swap_of_skeleton_eq hsk hG hxz hn)
          omega
        exact hH y (TransGen.head hyx (TransGen.head hHxz (TransGen.single hHzy)))
    · push Not at hadj
      have hvs : G.IsVStructure z y x := ⟨hzy, hxy, hzx, hadj.1, hadj.2⟩
      exact (hH.asymm hyx ((hv z y x).1 hvs).2.1).elim
  refine ⟨x, y, ⟨hxy, fun u => ⟨fun hu => ?_, ?_⟩⟩, hyx⟩
  · by_cases hux : u = x
    · exact Or.inl hux
    · exact Or.inr (h₂ u hu hux)
  · rintro (rfl | hu)
    · exact hxy
    · exact h₁ u hu

/-! ### Sequences of covered edge reversals -/

/-- Each covered edge reversal preserves Markov equivalence, so a sequence of them does. -/
theorem markovEquivalent_of_reflTransGen_coveredReversal [Finite V]
    (h : ReflTransGen CoveredReversal G H) : MarkovEquivalent G H := by
  induction h with
  | refl => exact MarkovEquivalent.refl _
  | tail _ hstep ih =>
    obtain ⟨hG', x, y, hc, rfl⟩ := hstep
    exact ih.trans (hc.markovEquivalent_reverseEdge hG')

/-- **Graphs with the same skeleton and v-structures are joined by covered edge reversals.** If
two acyclic graphs on a finite vertex type have the same skeleton and the same v-structures,
the second is obtained from the first by a sequence of covered edge reversals, each applied to
an acyclic graph (Chickering 1995). -/
theorem reflTransGen_coveredReversal [Finite V] (hG : G.IsAcyclic) (hH : H.IsAcyclic)
    (hsk : G.skeleton = H.skeleton)
    (hv : ∀ a c b, G.IsVStructure a c b ↔ H.IsVStructure a c b) :
    ReflTransGen CoveredReversal G H := by
  classical
  have := Fintype.ofFinite V
  let diff : Digraph V → Finset (V × V) := fun K =>
    univ.filter fun p => K.Adj p.1 p.2 ∧ ¬ H.Adj p.1 p.2
  suffices key : ∀ n, ∀ K : Digraph V, (diff K).card = n → K.IsAcyclic →
      K.skeleton = H.skeleton → (∀ a c b, K.IsVStructure a c b ↔ H.IsVStructure a c b) →
      ReflTransGen CoveredReversal K H from key _ G rfl hG hsk hv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hn hK hskK hvK
    by_cases hall : ∀ u v, K.Adj u v → H.Adj u v
    · rw [eq_of_skeleton_eq hskK hH hall]
    · push Not at hall
      obtain ⟨u, v, huv, hnuv⟩ := hall
      obtain ⟨x, y, hc, hyx⟩ := exists_isCovered_of_skeleton_eq hK hH hskK hvK
        ⟨u, v, huv, adj_swap_of_skeleton_eq hskK hK huv hnuv⟩
      set K' := K.reverseEdge x y
      have hK' : K'.IsAcyclic := hc.isAcyclic_reverseEdge hK
      have hsub : diff K' ⊆ (diff K).erase (x, y) := by
        intro p hp
        obtain ⟨-, hp₁, hp₂⟩ := mem_filter.1 hp
        rcases hp₁ with ⟨hp₁, hpne⟩ | ⟨h₁, h₂⟩
        · refine mem_erase.2 ⟨fun h => hpne ?_, mem_filter.2 ⟨mem_univ _, hp₁, hp₂⟩⟩
          subst h
          exact ⟨rfl, rfl⟩
        · exact absurd (h₁ ▸ h₂ ▸ hyx) hp₂
      have hmem : (x, y) ∈ diff K := mem_filter.2 ⟨mem_univ _, hc.1, hH.asymm hyx⟩
      have hlt : (diff K').card < n :=
        hn ▸ lt_of_le_of_lt (card_le_card hsub) (card_erase_lt_of_mem hmem)
      refine ReflTransGen.head ⟨hK, x, y, hc, rfl⟩ (ih _ hlt K' rfl hK' ?_ ?_)
      · rw [skeleton_reverseEdge hc.1, hskK]
      · intro a c b
        rw [hc.isVStructure_reverseEdge_iff hK, hvK]

/-! ### The characterization -/

/-- **Characterization of Markov equivalence** (Verma and Pearl 1990; Pearl 2009, Theorem 1.2.8).
Two acyclic directed graphs on the same finite vertex type have the same d-separation relation if
and only if they have the same skeleton and the same v-structures. -/
theorem markovEquivalent_iff [Finite V] (hG : G.IsAcyclic) (hH : H.IsAcyclic) :
    MarkovEquivalent G H ↔
      G.skeleton = H.skeleton ∧ ∀ a c b, G.IsVStructure a c b ↔ H.IsVStructure a c b :=
  ⟨fun h => ⟨h.skeleton_eq hG hH, fun _ _ _ => h.isVStructure_iff hG hH⟩,
    fun ⟨hsk, hv⟩ => markovEquivalent_of_reflTransGen_coveredReversal
      (reflTransGen_coveredReversal hG hH hsk hv)⟩

/-- **The transformational characterization** (Chickering 1995). Two acyclic graphs on a finite
vertex type are Markov equivalent if and only if one is obtained from the other by a sequence of
covered edge reversals. -/
theorem markovEquivalent_iff_reflTransGen_coveredReversal [Finite V] (hG : G.IsAcyclic)
    (hH : H.IsAcyclic) : MarkovEquivalent G H ↔ ReflTransGen CoveredReversal G H := by
  refine ⟨fun h => ?_, markovEquivalent_of_reflTransGen_coveredReversal⟩
  obtain ⟨hsk, hv⟩ := (markovEquivalent_iff hG hH).1 h
  exact reflTransGen_coveredReversal hG hH hsk hv

/-! ### Observational equivalence -/

/-- Markov equivalent acyclic graphs have the same factorizing distributions, for arbitrary
finite value types: factorization is the global Markov property, which only involves
d-separation. -/
theorem MarkovEquivalent.factorizes_iff [Fintype V] [DecidableEq V] {α : V → Type*}
    [∀ v, Fintype (α v)] [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : G.IsAcyclic) (hH : H.IsAcyclic) (h : MarkovEquivalent G H)
    {p : FiniteDist (∀ v, α v)} : G.Factorizes p ↔ H.Factorizes p := by
  classical
  rw [factorizes_iff_globalMarkov hG, factorizes_iff_globalMarkov hH]
  exact forall₃_congr fun X Y Z => by rw [h]

/-- **Markov equivalence is observational equivalence** (Pearl 2009, section 1.2.3): two acyclic
graphs on a finite vertex type have the same d-separation relation if and only if the same
distributions over binary variables factorize according to both. -/
theorem markovEquivalent_iff_forall_factorizes [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [DecidableRel H.Adj] (hG : G.IsAcyclic) (hH : H.IsAcyclic) :
    MarkovEquivalent G H ↔ ∀ p : FiniteDist (V → Bool), G.Factorizes p ↔ H.Factorizes p := by
  refine ⟨fun h p => h.factorizes_iff hG hH, fun h X Y Z => ?_⟩
  classical
  obtain ⟨X, rfl⟩ : ∃ X' : Finset V, (X' : Set V) = X := ⟨X.toFinset, Set.coe_toFinset X⟩
  obtain ⟨Y, rfl⟩ : ∃ Y' : Finset V, (Y' : Set V) = Y := ⟨Y.toFinset, Set.coe_toFinset Y⟩
  obtain ⟨Z, rfl⟩ : ∃ Z' : Finset V, (Z' : Set V) = Z := ⟨Z.toFinset, Set.coe_toFinset Z⟩
  rw [dSep_iff_forall_factorizes_condIndep' hG, dSep_iff_forall_factorizes_condIndep' hH]
  exact forall_congr' fun p => by rw [h p]

end Digraph
