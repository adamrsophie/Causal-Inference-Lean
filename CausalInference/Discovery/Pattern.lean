/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.MarkovEquivalenceCharacterization

/-!
# Compelled edges, patterns and the Meek rules

An edge `u → v` of an acyclic graph `G` is *compelled* when it has the same direction in every
acyclic graph Markov equivalent to `G`, and *reversible* otherwise. The *pattern* (essential
graph, completed partially directed acyclic graph) of `G` keeps the skeleton of `G`, directs the
compelled edges and leaves the reversible ones undirected (Verma and Pearl 1990; Pearl 2009,
*Causality*, 2nd edition, section 2.5).

A partially directed graph is represented by a `Digraph V`: the edge `u → v` is directed when
`P.Adj u v` and not `P.Adj v u`, and undirected, written `u ∼ v`, when both hold. The
orientation rules R1 to R4 of Verma and Pearl (1992) and Meek (1995), as printed in Pearl (2009,
section 2.5), are stated on such graphs and proved sound with respect to an invariant
(`Digraph.IsPartialPattern`): the skeleton is that of `G`, every directed edge is compelled in
`G`, and every v-structure of `G` is directed. The last condition is needed. In the collider
`a → b ← c` both edges are compelled, so a graph that directs `a → b` and leaves `b ∼ c`
undirected has only compelled directed edges; rule R1 then orients `b ∼ c` as `b → c`, which is
wrong.

## Main definitions

* `Digraph.IsCompelled G u v`, `Digraph.IsReversible G u v`, `Digraph.pattern G`.
* `Digraph.IsArrow P u v`, `Digraph.IsLine P u v`: directed and undirected edges of a partially
  directed graph.
* `Digraph.IsPartialPattern P G`: the soundness invariant.
* `Digraph.vStructurePattern G`: the skeleton of `G` with exactly the v-structures directed.
* `Digraph.MeekR1` to `Digraph.MeekR4`, `Digraph.MeekRule`, and the simultaneous application of
  all rules, `Digraph.meekPass`.

## Main results

* `Digraph.IsVStructure.isCompelled`: v-structure edges are compelled.
* `Digraph.isCompelled_or_isReversible`, `Digraph.pattern_isArrow_iff`,
  `Digraph.pattern_isLine_iff`, `Digraph.skeleton_pattern`.
* `Digraph.isPartialPattern_vStructurePattern`.
* `Digraph.IsPartialPattern.isCompelled_of_meekR1` to `...R4`,
  `Digraph.IsPartialPattern.isCompelled_of_meekRule`: **soundness of the Meek rules**.
* `Digraph.IsPartialPattern.meekPass`, `Digraph.IsPartialPattern.iterate_meekPass`: applying
  the rules keeps the invariant, so every edge the rules orient is compelled.

Completeness of the rules (Meek 1995: closing the v-structure pattern under the rules gives the
pattern) is not proved here.

## References

* T. Verma and J. Pearl (1990), *Equivalence and synthesis of causal models*.
* T. Verma and J. Pearl (1992), *An algorithm for deciding if a set of observed independencies
  has a causal explanation*.
* C. Meek (1995), *Causal inference and causal explanation with background knowledge*.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 2.5.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*} {G H P : Digraph V} {a b c d u v : V}

/-! ### Compelled and reversible edges -/

/-- The edge `u → v` of `G` is compelled: it is an edge of `G`, and of every acyclic graph that is
Markov equivalent to `G`. -/
def IsCompelled (G : Digraph V) (u v : V) : Prop :=
  G.Adj u v ∧ ∀ H : Digraph V, H.IsAcyclic → MarkovEquivalent G H → H.Adj u v

/-- The edge `u → v` of `G` is reversible: some acyclic graph Markov equivalent to `G` contains
the edge `v → u`. -/
def IsReversible (G : Digraph V) (u v : V) : Prop :=
  G.Adj u v ∧ ∃ H : Digraph V, H.IsAcyclic ∧ MarkovEquivalent G H ∧ H.Adj v u

/-- To show that `u → v` is compelled in an acyclic graph, it suffices to show that it lies in
every Markov equivalent acyclic graph. -/
theorem isCompelled_of_forall (hG : G.IsAcyclic)
    (h : ∀ H : Digraph V, H.IsAcyclic → MarkovEquivalent G H → H.Adj u v) :
    G.IsCompelled u v :=
  ⟨h G hG (MarkovEquivalent.refl G), h⟩

theorem IsVStructure.symm (h : G.IsVStructure a c b) : G.IsVStructure b c a :=
  ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.2, h.2.2.2.1⟩

/-- **The edges of a v-structure are compelled.** -/
theorem IsVStructure.isCompelled [Finite V] (hG : G.IsAcyclic) (h : G.IsVStructure a c b) :
    G.IsCompelled a c :=
  isCompelled_of_forall hG fun _ hH hGH => ((hGH.isVStructure_iff hG hH).1 h).1

/-- Every edge of a finite acyclic graph is either compelled or reversible, and not both. -/
theorem isCompelled_or_isReversible [Finite V] (hG : G.IsAcyclic) (h : G.Adj u v) :
    (G.IsCompelled u v ∨ G.IsReversible u v) ∧ ¬ (G.IsCompelled u v ∧ G.IsReversible u v) := by
  refine ⟨?_, fun ⟨⟨_, hc⟩, ⟨_, H, hH, hGH, hvu⟩⟩ => hH.asymm (hc H hH hGH) hvu⟩
  by_contra hn
  push Not at hn
  apply hn.1
  refine ⟨h, fun H hH hGH => ?_⟩
  have hsk := hGH.skeleton_eq hG hH
  have h' : H.skeleton.Adj u v := hsk ▸ skeleton_adj.2 ⟨hG.ne_of_adj h, Or.inl h⟩
  rcases (skeleton_adj.1 h').2 with h'' | h''
  · exact h''
  · exact absurd ⟨h, H, hH, hGH, h''⟩ hn.2

/-! ### Partially directed graphs -/

/-- In a partially directed graph `P`, the edge `u → v` is directed. -/
def IsArrow (P : Digraph V) (u v : V) : Prop := P.Adj u v ∧ ¬ P.Adj v u

/-- In a partially directed graph `P`, the edge `u ∼ v` is undirected. -/
def IsLine (P : Digraph V) (u v : V) : Prop := P.Adj u v ∧ P.Adj v u

theorem IsLine.symm (h : P.IsLine u v) : P.IsLine v u := ⟨h.2, h.1⟩

/-- The pattern of `G`: the skeleton of `G` in which the compelled edges are directed and the
other edges are undirected. -/
def pattern (G : Digraph V) : Digraph V where
  Adj u v := G.Adj u v ∨ (G.Adj v u ∧ ¬ G.IsCompelled v u)

/-- In the pattern, `u → v` is directed exactly when it is compelled. -/
theorem pattern_isArrow_iff (hG : G.IsAcyclic) :
    (pattern G).IsArrow u v ↔ G.IsCompelled u v := by
  constructor
  · rintro ⟨h₁ | ⟨h₁, -⟩, h₂⟩
    · by_contra hn
      exact h₂ (Or.inr ⟨h₁, hn⟩)
    · exact absurd (Or.inl h₁) h₂
  · intro h
    refine ⟨Or.inl h.1, ?_⟩
    rintro (h' | ⟨-, h'⟩)
    · exact hG.asymm h.1 h'
    · exact h' h

/-- In the pattern of a finite acyclic graph, `u ∼ v` is undirected exactly when one of the two
directions is a reversible edge of `G`. -/
theorem pattern_isLine_iff [Finite V] (hG : G.IsAcyclic) :
    (pattern G).IsLine u v ↔ G.IsReversible u v ∨ G.IsReversible v u := by
  constructor
  · rintro ⟨h₁ | ⟨h₁, hn₁⟩, h₂ | ⟨h₂, hn₂⟩⟩
    · exact absurd h₂ (hG.asymm h₁)
    · exact Or.inl (((isCompelled_or_isReversible hG h₁).1.resolve_left hn₂))
    · exact Or.inr (((isCompelled_or_isReversible hG h₂).1.resolve_left hn₁))
    · exact absurd h₂ (hG.asymm h₁)
  · rintro (h | h)
    · refine ⟨Or.inl h.1, Or.inr ⟨h.1, fun hc => ?_⟩⟩
      exact (isCompelled_or_isReversible hG h.1).2 ⟨hc, h⟩
    · refine ⟨Or.inr ⟨h.1, fun hc => ?_⟩, Or.inl h.1⟩
      exact (isCompelled_or_isReversible hG h.1).2 ⟨hc, h⟩

/-- The pattern has the skeleton of `G`. -/
theorem skeleton_pattern : (pattern G).skeleton = G.skeleton := by
  ext u v
  simp only [skeleton_adj, pattern]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ((h | ⟨h, -⟩) | (h | ⟨h, -⟩))
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)

/-! ### The soundness invariant -/

/-- `P` is a partial pattern for `G`: it has no loops, it has the skeleton of `G`, every directed
edge of `P` is compelled in `G`, and every v-structure `a → c ← b` of `G` is directed in `P`. -/
structure IsPartialPattern (P G : Digraph V) : Prop where
  irrefl : ∀ v, ¬ P.Adj v v
  skeleton_eq : P.skeleton = G.skeleton
  isCompelled : ∀ u v, P.IsArrow u v → G.IsCompelled u v
  isArrow_of_isVStructure : ∀ a c b, G.IsVStructure a c b → P.IsArrow a c

/-- In a partial pattern, adjacency (in either direction) is adjacency in every acyclic graph
with the skeleton of `G`. -/
theorem IsPartialPattern.adj_or_adj_iff (hP : P.IsPartialPattern G) (hH : H.IsAcyclic)
    (hsk : G.skeleton = H.skeleton) : P.Adj u v ∨ P.Adj v u ↔ H.Adj u v ∨ H.Adj v u := by
  by_cases huv : u = v
  · subst huv
    simp [hP.irrefl u, hH.irrefl u]
  · have h₁ : P.skeleton.Adj u v ↔ H.skeleton.Adj u v := by rw [hP.skeleton_eq, hsk]
    simpa [skeleton_adj, huv] using h₁

/-- An undirected edge `u ∼ w` of a partial pattern is never the edge `u → w` of a v-structure
`u → w ← b`. -/
theorem IsPartialPattern.not_isVStructure_of_isLine (hP : P.IsPartialPattern G)
    (h : P.IsLine u v) (b : V) : ¬ G.IsVStructure u v b :=
  fun hv => (hP.isArrow_of_isVStructure u v b hv).2 h.2

/-- Rule R1: orient `b ∼ c` as `b → c` when some `a → b` has `a` and `c` nonadjacent. -/
def MeekR1 (P : Digraph V) (b c : V) : Prop :=
  P.IsLine b c ∧ ∃ a, P.IsArrow a b ∧ a ≠ c ∧ ¬ P.Adj a c ∧ ¬ P.Adj c a

/-- Rule R2: orient `a ∼ b` as `a → b` when there is a chain `a → c → b`. -/
def MeekR2 (P : Digraph V) (a b : V) : Prop :=
  P.IsLine a b ∧ ∃ c, P.IsArrow a c ∧ P.IsArrow c b

/-- Rule R3: orient `a ∼ b` as `a → b` when there are chains `a ∼ c → b` and `a ∼ d → b` with
`c` and `d` nonadjacent. -/
def MeekR3 (P : Digraph V) (a b : V) : Prop :=
  P.IsLine a b ∧ ∃ c d, P.IsLine a c ∧ P.IsArrow c b ∧ P.IsLine a d ∧ P.IsArrow d b ∧ c ≠ d ∧
    ¬ P.Adj c d ∧ ¬ P.Adj d c

/-- Rule R4: orient `a ∼ b` as `a → b` when there are chains `a ∼ c → d` and `c → d → b` with
`c` and `b` nonadjacent and `a` and `d` adjacent. The adjacency of `a` and `d` is part of the
rule as printed in Pearl (2009); the soundness proof does not use it. -/
def MeekR4 (P : Digraph V) (a b : V) : Prop :=
  P.IsLine a b ∧ ∃ c d, P.IsLine a c ∧ P.IsArrow c d ∧ P.IsArrow d b ∧ c ≠ b ∧
    ¬ P.Adj c b ∧ ¬ P.Adj b c ∧ (P.Adj a d ∨ P.Adj d a)

/-- Some orientation rule orients `a ∼ b` as `a → b`. -/
def MeekRule (P : Digraph V) (a b : V) : Prop :=
  MeekR1 P a b ∨ MeekR2 P a b ∨ MeekR3 P a b ∨ MeekR4 P a b

theorem MeekRule.isLine (h : MeekRule P a b) : P.IsLine a b := by
  rcases h with h | h | h | h <;> exact h.1

/-- Nonadjacency in a partial pattern is nonadjacency in every Markov equivalent acyclic
graph. -/
theorem IsPartialPattern.not_adj_of_not_adj (hP : P.IsPartialPattern G) (hH : H.IsAcyclic)
    (hsk : G.skeleton = H.skeleton) (h₁ : ¬ P.Adj u v) (h₂ : ¬ P.Adj v u) :
    ¬ H.Adj u v ∧ ¬ H.Adj v u := by
  have := (hP.adj_or_adj_iff hH hsk (u := u) (v := v)).not
  push Not at this
  exact this.1 ⟨h₁, h₂⟩

/-- **Soundness of rule R1.** -/
theorem IsPartialPattern.isCompelled_of_meekR1 [Finite V] (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic)
    (h : MeekR1 P b c) : G.IsCompelled b c := by
  obtain ⟨hbc, a, hab, hac, hn₁, hn₂⟩ := h
  refine isCompelled_of_forall hG fun H hH hGH => ?_
  obtain ⟨hsk, hv⟩ := (markovEquivalent_iff hG hH).1 hGH
  have hHab : H.Adj a b := (hP.isCompelled a b hab).2 H hH hGH
  rcases (hP.adj_or_adj_iff hH hsk).1 (Or.inl hbc.1) with h | hcb
  · exact h
  · obtain ⟨hn₁', hn₂'⟩ := hP.not_adj_of_not_adj hH hsk hn₁ hn₂
    exact absurd ((hv a b c).2 ⟨hHab, hcb, hac, hn₁', hn₂'⟩).symm
      (hP.not_isVStructure_of_isLine hbc.symm a)

/-- **Soundness of rule R2.** -/
theorem IsPartialPattern.isCompelled_of_meekR2 (hP : P.IsPartialPattern G) (hG : G.IsAcyclic)
    (h : MeekR2 P a b) : G.IsCompelled a b := by
  obtain ⟨hab, c, hac, hcb⟩ := h
  refine isCompelled_of_forall hG fun H hH hGH => ?_
  have hsk := hGH.skeleton_eq hG hH
  have h₁ : H.Adj a c := (hP.isCompelled a c hac).2 H hH hGH
  have h₂ : H.Adj c b := (hP.isCompelled c b hcb).2 H hH hGH
  rcases (hP.adj_or_adj_iff hH hsk).1 (Or.inl hab.1) with h | hba
  · exact h
  · exact absurd (TransGen.head h₁ (TransGen.head h₂ (TransGen.single hba))) (hH a)

/-- **Soundness of rule R3.** -/
theorem IsPartialPattern.isCompelled_of_meekR3 [Finite V] (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic)
    (h : MeekR3 P a b) : G.IsCompelled a b := by
  obtain ⟨hab, c, d, hac, hcb, had, hdb, hcd, hn₁, hn₂⟩ := h
  refine isCompelled_of_forall hG fun H hH hGH => ?_
  obtain ⟨hsk, hv⟩ := (markovEquivalent_iff hG hH).1 hGH
  have h₁ : H.Adj c b := (hP.isCompelled c b hcb).2 H hH hGH
  have h₂ : H.Adj d b := (hP.isCompelled d b hdb).2 H hH hGH
  rcases (hP.adj_or_adj_iff hH hsk).1 (Or.inl hab.1) with h | hba
  · exact h
  · exfalso
    have hca : H.Adj c a := by
      rcases (hP.adj_or_adj_iff hH hsk).1 (Or.inl hac.1) with h | h
      · exact absurd (TransGen.head h (TransGen.head h₁ (TransGen.single hba))) (hH a)
      · exact h
    have hda : H.Adj d a := by
      rcases (hP.adj_or_adj_iff hH hsk).1 (Or.inl had.1) with h | h
      · exact absurd (TransGen.head h (TransGen.head h₂ (TransGen.single hba))) (hH a)
      · exact h
    obtain ⟨hn₁', hn₂'⟩ := hP.not_adj_of_not_adj hH hsk hn₁ hn₂
    exact hP.not_isVStructure_of_isLine hac.symm d ((hv c a d).2 ⟨hca, hda, hcd, hn₁', hn₂'⟩)

/-- **Soundness of rule R4.** -/
theorem IsPartialPattern.isCompelled_of_meekR4 [Finite V] (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic)
    (h : MeekR4 P a b) : G.IsCompelled a b := by
  obtain ⟨hab, c, d, hac, hcd, hdb, hcb, hn₁, hn₂, -⟩ := h
  refine isCompelled_of_forall hG fun H hH hGH => ?_
  obtain ⟨hsk, hv⟩ := (markovEquivalent_iff hG hH).1 hGH
  have h₁ : H.Adj c d := (hP.isCompelled c d hcd).2 H hH hGH
  have h₂ : H.Adj d b := (hP.isCompelled d b hdb).2 H hH hGH
  rcases (hP.adj_or_adj_iff hH hsk).1 (Or.inl hab.1) with h | hba
  · exact h
  · exfalso
    have hca : H.Adj c a := by
      rcases (hP.adj_or_adj_iff hH hsk).1 (Or.inl hac.1) with h | h
      · exact absurd (TransGen.head h (TransGen.head h₁ (TransGen.head h₂
          (TransGen.single hba)))) (hH a)
      · exact h
    obtain ⟨hn₁', hn₂'⟩ := hP.not_adj_of_not_adj hH hsk hn₁ hn₂
    exact hP.not_isVStructure_of_isLine hac.symm b ((hv c a b).2 ⟨hca, hba, hcb, hn₁', hn₂'⟩)

/-- **Soundness of the Meek rules.** In a partial pattern for a finite acyclic graph `G`, every
edge that one of the rules R1 to R4 orients is compelled in `G`. -/
theorem IsPartialPattern.isCompelled_of_meekRule [Finite V] (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic)
    (h : MeekRule P a b) : G.IsCompelled a b := by
  rcases h with h | h | h | h
  · exact hP.isCompelled_of_meekR1 hG h
  · exact hP.isCompelled_of_meekR2 hG h
  · exact hP.isCompelled_of_meekR3 hG h
  · exact hP.isCompelled_of_meekR4 hG h

/-! ### Applying the rules -/

/-- One pass of the rules: every undirected edge `a ∼ b` that some rule orients as `a → b`
(judged on `P`) is oriented, by removing `b → a`; all such edges are oriented simultaneously. -/
def meekPass (P : Digraph V) : Digraph V where
  Adj u v := P.Adj u v ∧ ¬ MeekRule P v u

/-- **Applying the rules keeps the invariant.** One pass of the rules on a partial pattern for a
finite acyclic graph `G` gives a partial pattern for `G`. -/
theorem IsPartialPattern.meekPass [Finite V] (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic) :
    (meekPass P).IsPartialPattern G := by
  have hc := fun {a b} (h : MeekRule P a b) => hP.isCompelled_of_meekRule hG h
  refine ⟨fun v h => hP.irrefl v h.1, ?_, ?_, ?_⟩
  · rw [← hP.skeleton_eq]
    ext u v
    simp only [skeleton_adj, Digraph.meekPass]
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
    · have key : ∀ {u v}, P.Adj u v → (P.Adj u v ∧ ¬ MeekRule P v u) ∨
          (P.Adj v u ∧ ¬ MeekRule P u v) := by
        intro u v h
        by_cases h₁ : MeekRule P v u
        · refine Or.inr ⟨h₁.isLine.1, fun h₂ => ?_⟩
          exact hG.asymm (hc h₁).1 (hc h₂).1
        · exact Or.inl ⟨h, h₁⟩
      rintro (h | h)
      · exact key h
      · exact (key h).symm
  · rintro u v ⟨⟨huv, -⟩, hvu⟩
    by_cases h : P.Adj v u
    · by_contra hn
      apply hvu
      refine ⟨h, fun hr => hn (hc hr)⟩
    · exact hP.isCompelled u v ⟨huv, h⟩
  · intro a c b hv
    obtain ⟨h₁, h₂⟩ := hP.isArrow_of_isVStructure a c b hv
    exact ⟨⟨h₁, fun h => h₂ h.isLine.1⟩, fun h => h₂ h.1⟩

/-- Any number of passes of the rules keeps the invariant. -/
theorem IsPartialPattern.iterate_meekPass [Finite V] (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic)
    (n : ℕ) : (Digraph.meekPass^[n] P).IsPartialPattern G := by
  induction n with
  | zero => exact hP
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.meekPass hG

/-- Every edge directed by repeated passes of the rules from a partial pattern is compelled. -/
theorem IsPartialPattern.isCompelled_of_iterate [Finite V] (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic)
    (n : ℕ) (h : (Digraph.meekPass^[n] P).IsArrow u v) : G.IsCompelled u v :=
  (hP.iterate_meekPass hG n).isCompelled u v h

/-! ### The v-structure pattern -/

/-- The v-structure pattern of `G`: the skeleton of `G` with exactly the edges of the
v-structures directed. -/
def vStructurePattern (G : Digraph V) : Digraph V where
  Adj u v := G.skeleton.Adj u v ∧ ¬ ∃ w, G.IsVStructure v u w

/-- The v-structure pattern of a finite acyclic graph is a partial pattern for it. -/
theorem isPartialPattern_vStructurePattern [Finite V] (hG : G.IsAcyclic) :
    (vStructurePattern G).IsPartialPattern G := by
  refine ⟨fun v h => h.1.ne rfl, ?_, ?_, ?_⟩
  · ext u v
    simp only [skeleton_adj, vStructurePattern]
    refine and_congr_right fun huv => ⟨?_, ?_⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact h.2
      · exact h.2.symm
    · intro h
      by_cases h₁ : ∃ w, G.IsVStructure v u w
      · obtain ⟨w, hw⟩ := h₁
        refine Or.inr ⟨⟨huv.symm, h.symm⟩, ?_⟩
        rintro ⟨w', hw'⟩
        exact hG.asymm hw.1 hw'.1
      · exact Or.inl ⟨⟨huv, h⟩, h₁⟩
  · rintro u v ⟨huv, h⟩
    simp only [vStructurePattern, not_and, not_not] at h
    obtain ⟨w, hw⟩ := h huv.1.symm
    exact hw.isCompelled hG
  · intro a c b hv
    refine ⟨⟨skeleton_adj.2 ⟨hG.ne_of_adj hv.1, Or.inl hv.1⟩, ?_⟩, fun h => h.2 ⟨b, hv⟩⟩
    rintro ⟨w, hw⟩
    exact hG.asymm hv.1 hw.1

/-! ### Decidability -/

section Decidable

variable [DecidableEq V]

instance decidableIsVStructure [DecidableRel G.Adj] (a c b : V) :
    Decidable (G.IsVStructure a c b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance decidableRelSkeleton [DecidableRel G.Adj] : DecidableRel G.skeleton.Adj :=
  fun _ _ => decidable_of_iff _ skeleton_adj.symm

instance decidableIsArrow [DecidableRel P.Adj] (u v : V) : Decidable (P.IsArrow u v) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance decidableIsLine [DecidableRel P.Adj] (u v : V) : Decidable (P.IsLine u v) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable [Fintype V]

instance decidableRelVStructurePattern [DecidableRel G.Adj] :
    DecidableRel (vStructurePattern G).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

instance decidableMeekR1 [DecidableRel P.Adj] (a b : V) : Decidable (MeekR1 P a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance decidableMeekR2 [DecidableRel P.Adj] (a b : V) : Decidable (MeekR2 P a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance decidableMeekR3 [DecidableRel P.Adj] (a b : V) : Decidable (MeekR3 P a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance decidableMeekR4 [DecidableRel P.Adj] (a b : V) : Decidable (MeekR4 P a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance decidableMeekRule [DecidableRel P.Adj] (a b : V) : Decidable (MeekRule P a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

instance decidableRelMeekPass [DecidableRel P.Adj] : DecidableRel (meekPass P).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

end Decidable

end Digraph
