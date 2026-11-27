/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Discovery.Faithfulness
public import CausalInference.Discovery.Pattern

/-!
# The PC algorithm with an independence oracle

The PC algorithm of Spirtes and Glymour (1991) (Pearl 2009, *Causality*, 2nd edition, section
2.5) recovers the pattern of an acyclic graph from conditional independence queries. Here the
queries are answered by an *oracle* `I : V → V → Finset V → Prop`, read as "`x` and `y` are
independent given `S`". The algorithm has three phases.

1. **Adjacency search.** Start from the complete graph. At level `ℓ = 0, 1, 2, …`, remove the
   edge `x ∼ y` when some set `S` of size `ℓ`, drawn from the current neighbors of `x` other than
   `y` or from the current neighbors of `y` other than `x`, has `I x y S` or `I y x S`. All the
   edges are tested against the neighborhoods at the start of the level, so the result does not
   depend on an order of the vertices (the order-independent variant of Colombo and Maathuis
   2014). Levels `0` to `card V - 1` are run.
2. **Colliders.** For nonadjacent `a ≠ b` with a common neighbor `c`, orient `a → c ← b` when
   some set that separated `a` and `b` at the level where their edge was removed does not
   contain `c`. Every set recorded at that level is used, so no choice is involved.
3. **Orientation rules.** Apply the rules R1 to R4 (`Digraph.meekPass`) `(card V) ^ 2` times.

All phases are computable functions of the oracle on finite vertex types with decidable
equality; the graphs are finsets of ordered pairs.

## Correctness

Faithfulness is an explicit hypothesis, never part of the oracle: the correctness theorems
assume that the oracle answers d-separation in an acyclic graph `G`
(`hI : ∀ x y S, I x y S ↔ G.DSep {x} {y} ↑S`). By
`CausalInference.FiniteDist.IsFaithful.condIndep_iff_dSep` this holds for the conditional
independence oracle of any law that is Markov and faithful to `G`
(`Digraph.condIndep_oracle_iff_dSep`). Under this hypothesis:

* `Digraph.mem_pcAdj_iff`: the adjacency phase returns the skeleton of `G`;
* `Digraph.isPCCollider_iff`: the collider phase finds exactly the v-structures of `G`, and
  `Digraph.toDigraph_pcColliders`: the partially directed graph after it is the v-structure
  pattern of `G`;
* `Digraph.pcOutput_isPartialPattern`, `Digraph.pcOutput_isCompelled`: the output has the
  skeleton of `G` and every edge it orients is compelled in `G`;
* `Digraph.pcOutput_eq_pattern`: if the rules are complete in the sense of Meek (1995)
  (`Digraph.MeekComplete`), the output is the pattern of `G`. The completeness is proved in
  `CausalInference.Discovery.PatternCompleteness` (`Digraph.meekComplete`), which gives the
  unconditional `Digraph.pcOutput_eq_pattern'`.

Without faithfulness the algorithm can fail: with the exclusive-or law, which is Markov to the
collider `0 → 2 ← 1` but not faithful to it, the independence oracle removes the edge `0 ∼ 2`
(`CausalInference.GraphExamples.xor_pcAdj_ne_skeleton`).

## References

* P. Spirtes and C. Glymour (1991), *An algorithm for fast recovery of sparse causal graphs*.
* P. Spirtes, C. Glymour and R. Scheines (1993), *Causation, Prediction, and Search*.
* C. Meek (1995), *Causal inference and causal explanation with background knowledge*.
* D. Colombo and M. H. Maathuis (2014), *Order-independent constraint-based causal structure
  learning*.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 2.5.
-/

@[expose] public section

namespace Digraph

open Finset Relation

variable {V : Type*}

/-- The partially directed graph with the arcs of a finset of ordered pairs. -/
def toDigraph (A : Finset (V × V)) : Digraph V where
  Adj u v := (u, v) ∈ A

instance decidableRelToDigraph [DecidableEq V] (A : Finset (V × V)) :
    DecidableRel (toDigraph A).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ A))

@[simp] theorem toDigraph_adj {A : Finset (V × V)} {u v : V} :
    (toDigraph A).Adj u v ↔ (u, v) ∈ A := Iff.rfl

variable [Fintype V] [DecidableEq V]

/-! ### The algorithm -/

section Algorithm

variable (I : V → V → Finset V → Prop) [∀ x y S, Decidable (I x y S)]

/-- The conditioning sets of size `ℓ` tested for the edge `x ∼ y` in the current graph `A`: the
sets of `ℓ` neighbors of `x` other than `y`, and of `ℓ` neighbors of `y` other than `x`. -/
def candidates (A : Finset (V × V)) (x y : V) (ℓ : ℕ) : Finset (Finset V) :=
  (univ.filter fun z => (x, z) ∈ A ∧ z ≠ y).powersetCard ℓ ∪
    (univ.filter fun z => (y, z) ∈ A ∧ z ≠ x).powersetCard ℓ

/-- The edge `x ∼ y` is removed at level `ℓ` from `A`: the oracle declares `x` and `y` independent
given some candidate set. -/
def RemovedAt (A : Finset (V × V)) (x y : V) (ℓ : ℕ) : Prop :=
  ∃ S ∈ candidates A x y ℓ, I x y S ∨ I y x S

instance (A : Finset (V × V)) (x y : V) (ℓ : ℕ) : Decidable (RemovedAt I A x y ℓ) :=
  inferInstanceAs (Decidable (∃ S ∈ _, _))

/-- One level of the adjacency search: remove every edge that is removed at level `ℓ`, judged on
the graph at the start of the level. -/
def levelStep (ℓ : ℕ) (A : Finset (V × V)) : Finset (V × V) :=
  A.filter fun p => ¬ RemovedAt I A p.1 p.2 ℓ

/-- The graph after the levels `0` to `ℓ - 1`, starting from the complete graph. -/
def adjAt : ℕ → Finset (V × V)
  | 0 => univ.filter fun p => p.1 ≠ p.2
  | ℓ + 1 => levelStep I ℓ (adjAt ℓ)

/-- The adjacency phase: the graph after the levels `0` to `card V - 1`. -/
def pcAdj : Finset (V × V) := adjAt I (Fintype.card V)

/-- The collider test for `a ∼ c ∼ b`: at some level where the edge `a ∼ b` was still present, a
candidate set not containing `c` separated `a` and `b`. -/
def SepWithout (a b c : V) : Prop :=
  ∃ ℓ < Fintype.card V, (a, b) ∈ adjAt I ℓ ∧
    ∃ S ∈ candidates (adjAt I ℓ) a b ℓ, (I a b S ∨ I b a S) ∧ c ∉ S

instance (a b c : V) : Decidable (SepWithout I a b c) :=
  inferInstanceAs (Decidable (∃ ℓ < _, _))

/-- `a → c ← b` is oriented by the collider phase: `a ∼ c ∼ b` in the adjacency output, `a ≠ b`
nonadjacent, and the collider test succeeds. -/
def IsPCCollider (a c b : V) : Prop :=
  (a, c) ∈ pcAdj I ∧ (c, b) ∈ pcAdj I ∧ a ≠ b ∧ (a, b) ∉ pcAdj I ∧ SepWithout I a b c

instance (a c b : V) : Decidable (IsPCCollider I a c b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The collider phase: the adjacency output with the arc `c → a` removed for every oriented
collider `a → c ← b`. -/
def pcColliders : Finset (V × V) :=
  (pcAdj I).filter fun p => ¬ ∃ w, IsPCCollider I p.2 p.1 w

/-- One pass of the orientation rules on a finset of arcs. -/
def meekPassF (A : Finset (V × V)) : Finset (V × V) :=
  A.filter fun p => ¬ MeekRule (toDigraph A) p.2 p.1

/-- The output of the PC algorithm: `(card V) ^ 2` passes of the rules after the collider
phase. -/
def pcOutput : Finset (V × V) := meekPassF^[Fintype.card V ^ 2] (pcColliders I)

end Algorithm

theorem toDigraph_meekPassF (A : Finset (V × V)) :
    toDigraph (meekPassF A) = meekPass (toDigraph A) := by
  ext u v
  simp [meekPassF, Digraph.meekPass]

theorem toDigraph_iterate_meekPassF (A : Finset (V × V)) (n : ℕ) :
    toDigraph (meekPassF^[n] A) = Digraph.meekPass^[n] (toDigraph A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', toDigraph_meekPassF, ih]

/-! ### Elementary facts about the adjacency search -/

section Elementary

variable {I : V → V → Finset V → Prop} [∀ x y S, Decidable (I x y S)]

theorem candidates_comm (A : Finset (V × V)) (x y : V) (ℓ : ℕ) :
    candidates A x y ℓ = candidates A y x ℓ := union_comm _ _

omit [∀ x y S, Decidable (I x y S)] in
theorem removedAt_comm {A : Finset (V × V)} {x y : V} {ℓ : ℕ} :
    RemovedAt I A x y ℓ ↔ RemovedAt I A y x ℓ := by
  unfold RemovedAt
  rw [candidates_comm]
  exact exists_congr fun _ => and_congr_right fun _ => or_comm

theorem adjAt_succ_subset (ℓ : ℕ) : adjAt I (ℓ + 1) ⊆ adjAt I ℓ := filter_subset _ _

theorem adjAt_anti {ℓ m : ℕ} (h : ℓ ≤ m) : adjAt I m ⊆ adjAt I ℓ := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact (adjAt_succ_subset _).trans ih

theorem ne_of_mem_adjAt {ℓ : ℕ} {x y : V} (h : (x, y) ∈ adjAt I ℓ) : x ≠ y := by
  have h0 := adjAt_anti (I := I) (Nat.zero_le ℓ) h
  exact (mem_filter.1 h0).2

theorem mem_adjAt_comm {ℓ : ℕ} {x y : V} : (x, y) ∈ adjAt I ℓ ↔ (y, x) ∈ adjAt I ℓ := by
  induction ℓ generalizing x y with
  | zero => simp [adjAt, eq_comm]
  | succ ℓ ih =>
    simp only [adjAt, levelStep, mem_filter]
    exact and_congr ih (not_congr removedAt_comm)

/-- A candidate set contains neither endpoint. -/
theorem notMem_of_mem_candidates {ℓ : ℕ} {x y : V} {S : Finset V}
    (hS : S ∈ candidates (adjAt I ℓ) x y ℓ) : x ∉ S ∧ y ∉ S := by
  rcases mem_union.1 hS with h | h <;> obtain ⟨h, -⟩ := mem_powersetCard.1 h
  · refine ⟨fun hx => ?_, fun hy => ?_⟩
    · exact ne_of_mem_adjAt (mem_filter.1 (h hx)).2.1 rfl
    · exact (mem_filter.1 (h hy)).2.2 rfl
  · refine ⟨fun hx => ?_, fun hy => ?_⟩
    · exact (mem_filter.1 (h hx)).2.2 rfl
    · exact ne_of_mem_adjAt (mem_filter.1 (h hy)).2.1 rfl

/-- If the edge `x ∼ y` is present at level `0` and absent at level `n`, it is removed at some
level below `n`. -/
theorem exists_removedAt {n : ℕ} {x y : V} (h0 : (x, y) ∈ adjAt I 0)
    (hn : (x, y) ∉ adjAt I n) :
    ∃ ℓ < n, (x, y) ∈ adjAt I ℓ ∧ RemovedAt I (adjAt I ℓ) x y ℓ := by
  induction n with
  | zero => exact absurd h0 hn
  | succ n ih =>
    by_cases hm : (x, y) ∈ adjAt I n
    · refine ⟨n, Nat.lt_succ_self n, hm, ?_⟩
      by_contra hr
      exact hn (mem_filter.2 ⟨hm, hr⟩)
    · obtain ⟨ℓ, hℓ, h⟩ := ih hm
      exact ⟨ℓ, Nat.lt_succ_of_lt hℓ, h⟩

/-- If the oracle declares `x` and `y` independent given the empty set, the adjacency phase
removes the edge `x ∼ y`. -/
theorem notMem_pcAdj_of_empty {x y : V} (h : I x y ∅) : (x, y) ∉ pcAdj I := by
  intro hxy
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨x⟩
  have h1 : (x, y) ∈ adjAt I 1 := adjAt_anti (I := I) hpos hxy
  have h0 : (x, y) ∈ adjAt I 0 := adjAt_succ_subset 0 h1
  refine (mem_filter.1 h1).2 ⟨∅, mem_union.2 (Or.inl ?_), Or.inl h⟩
  exact mem_powersetCard.2 ⟨empty_subset _, card_empty⟩

end Elementary

/-! ### Correctness under a d-separation oracle -/

section Correctness

variable {I : V → V → Finset V → Prop} [∀ x y S, Decidable (I x y S)] {G : Digraph V}

/-- The conditional independence oracle of a law that is Markov and faithful to `G` answers
d-separation in `G`. -/
theorem condIndep_oracle_iff_dSep {α : V → Type*} [∀ v, Fintype (α v)]
    [∀ v, DecidableEq (α v)] {p : CausalInference.FiniteDist (∀ v, α v)}
    (hM : G.GlobalMarkov p) (hF : p.IsFaithful G) (x y : V) (S : Finset V) :
    p.CondIndep {x} {y} S ↔ G.DSep {x} {y} ↑S := by
  rw [hF.condIndep_iff_dSep hM, coe_singleton, coe_singleton]

variable (hI : ∀ x y S, I x y S ↔ G.DSep {x} {y} ↑S)
include hI

omit [Fintype V] [DecidableEq V] [∀ x y S, Decidable (I x y S)] in
/-- A set the oracle accepts, in either order, separates the two vertices. -/
theorem dSep_of_oracle {x y : V} {S : Finset V} (h : I x y S ∨ I y x S) :
    G.DSep {x} {y} ↑S := by
  rcases h with h | h
  · exact (hI x y S).1 h
  · exact ((hI y x S).1 h).symm

/-- The adjacency search never removes an edge of `G`. -/
theorem mem_adjAt_of_skeleton_adj {x y : V} (h : G.skeleton.Adj x y) (ℓ : ℕ) :
    (x, y) ∈ adjAt I ℓ := by
  induction ℓ with
  | zero => exact mem_filter.2 ⟨mem_univ _, h.ne⟩
  | succ ℓ ih =>
    refine mem_filter.2 ⟨ih, fun ⟨S, hS, hI'⟩ => ?_⟩
    obtain ⟨hx, hy⟩ := notMem_of_mem_candidates hS
    exact not_dSep_of_skeleton_adj h hx hy (dSep_of_oracle hI hI')

/-- In an acyclic graph a vertex `v` that does not reach `u` is separated from `u` by its
parents, which the adjacency search tests as a candidate set at the level of their number. -/
theorem notMem_adjAt_of_not_reflTransGen (hG : G.IsAcyclic) [DecidableRel G.Adj] {v u : V}
    (hvu : ¬ ReflTransGen G.Adj v u) (hn : ¬ G.skeleton.Adj v u) (hne : v ≠ u) :
    (v, u) ∉ adjAt I ((G.parentsFinset v).card + 1) := by
  intro hmem
  set ℓ := (G.parentsFinset v).card
  have hℓ : (v, u) ∈ adjAt I ℓ := adjAt_succ_subset ℓ hmem
  refine (mem_filter.1 hmem).2 ⟨G.parentsFinset v, mem_union.2 (Or.inl ?_), Or.inl ?_⟩
  · refine mem_powersetCard.2 ⟨fun z hz => mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, rfl⟩
    · have hzv : G.Adj z v := mem_parentsFinset.1 hz
      exact mem_adjAt_of_skeleton_adj hI (skeleton_adj.2 ⟨(hG.ne_of_adj hzv).symm,
        Or.inr hzv⟩) ℓ
    · rintro rfl
      exact hn (skeleton_adj.2 ⟨hne, Or.inr (mem_parentsFinset.1 hz)⟩)
  · rw [hI, coe_parentsFinset]
    exact hG.dSep_parents_of_not_reflTransGen hvu

/-- The adjacency search removes every edge that is not in `G`. -/
theorem notMem_pcAdj_of_not_adj (hG : G.IsAcyclic) {x y : V} (hn : ¬ G.skeleton.Adj x y) :
    (x, y) ∉ pcAdj I := by
  classical
  intro hxy
  have hne : x ≠ y := ne_of_mem_adjAt hxy
  have hcard : ∀ v, (G.parentsFinset v).card + 1 ≤ Fintype.card V := fun v => by
    have : G.parentsFinset v ⊆ univ.erase v := fun z hz =>
      mem_erase.2 ⟨fun h => by subst h; exact hG.irrefl _ (mem_parentsFinset.1 hz), mem_univ z⟩
    have := card_le_card this
    rw [card_erase_of_mem (mem_univ v), card_univ] at this
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
    omega
  by_cases hyx : ReflTransGen G.Adj y x
  · have hxy' : ¬ ReflTransGen G.Adj x y := by
      intro h
      rcases reflTransGen_iff_eq_or_transGen.1 hyx with e | e
      · exact hne e
      · rcases reflTransGen_iff_eq_or_transGen.1 h with e' | e'
        · exact hne e'.symm
        · exact hG y (e.trans e')
    exact notMem_adjAt_of_not_reflTransGen hI hG hxy' hn hne (adjAt_anti (hcard x) hxy)
  · have hn' : ¬ G.skeleton.Adj y x := fun h => hn h.symm
    exact notMem_adjAt_of_not_reflTransGen hI hG hyx hn' hne.symm
      (adjAt_anti (hcard y) (mem_adjAt_comm.1 hxy))

/-- **The adjacency phase returns the skeleton.** Under a d-separation oracle of an acyclic
graph `G`, the edge `x ∼ y` survives the adjacency search if and only if `x` and `y` are adjacent
in `G`. -/
theorem mem_pcAdj_iff (hG : G.IsAcyclic) {x y : V} :
    (x, y) ∈ pcAdj I ↔ G.skeleton.Adj x y :=
  ⟨fun h => by_contra fun hn => notMem_pcAdj_of_not_adj hI hG hn h,
    fun h => mem_adjAt_of_skeleton_adj hI h _⟩

/-- **The collider phase finds exactly the v-structures.** Under a d-separation oracle of a
finite acyclic graph `G`, the collider phase orients `a → c ← b` if and only if it is a
v-structure of `G`. -/
theorem isPCCollider_iff (hG : G.IsAcyclic) {a c b : V} :
    IsPCCollider I a c b ↔ G.IsVStructure a c b := by
  rw [hG.isVStructure_iff]
  constructor
  · rintro ⟨hac, hcb, hab, hnab, ℓ, -, -, S, hS, hsep, hc⟩
    rw [mem_pcAdj_iff hI hG] at hac hcb hnab
    have hs : G.IsUnshielded a c b := ⟨hab, hac, hcb, hnab⟩
    obtain ⟨ha, hb⟩ := notMem_of_mem_candidates hS
    exact ⟨hs, (hG.collider_iff_exists_dSep hs).2
      ⟨↑S, ha, hb, dSep_of_oracle hI hsep, hc⟩⟩
  · rintro ⟨hs, hcol⟩
    obtain ⟨hab, hac, hcb, hnab⟩ := hs
    have hnab' : (a, b) ∉ pcAdj I := fun h => hnab ((mem_pcAdj_iff hI hG).1 h)
    obtain ⟨ℓ, hℓ, hmem, S, hS, hsep⟩ :=
      exists_removedAt (mem_filter.2 ⟨mem_univ _, hab⟩) hnab'
    obtain ⟨ha, hb⟩ := notMem_of_mem_candidates hS
    have hcS : c ∉ (S : Set V) := (hG.collider_iff_forall_dSep ⟨hab, hac, hcb, hnab⟩).1 hcol
      ↑S ha hb (dSep_of_oracle hI hsep)
    exact ⟨(mem_pcAdj_iff hI hG).2 hac, (mem_pcAdj_iff hI hG).2 hcb, hab, hnab',
      ℓ, hℓ, hmem, S, hS, hsep, hcS⟩

/-- **After the collider phase.** Under a d-separation oracle of a finite acyclic graph `G`, the
partially directed graph after the collider phase is the v-structure pattern of `G`. -/
theorem toDigraph_pcColliders (hG : G.IsAcyclic) :
    toDigraph (pcColliders I) = vStructurePattern G := by
  ext u v
  simp only [toDigraph_adj, pcColliders, mem_filter, vStructurePattern, mem_pcAdj_iff hI hG,
    isPCCollider_iff hI hG]

/-- The output of the PC algorithm under a d-separation oracle of a finite acyclic graph `G` is a
partial pattern for `G`: it has the skeleton of `G`, directs every v-structure, and every edge
it directs is compelled. -/
theorem pcOutput_isPartialPattern (hG : G.IsAcyclic) :
    (toDigraph (pcOutput I)).IsPartialPattern G := by
  rw [pcOutput, toDigraph_iterate_meekPassF, toDigraph_pcColliders hI hG]
  exact (isPartialPattern_vStructurePattern hG).iterate_meekPass hG _

/-- **Every edge the PC algorithm orients is compelled.** -/
theorem pcOutput_isCompelled (hG : G.IsAcyclic) {u v : V}
    (h : (toDigraph (pcOutput I)).IsArrow u v) : G.IsCompelled u v :=
  (pcOutput_isPartialPattern hI hG).isCompelled u v h

/-- The output of the PC algorithm has the skeleton of `G`. -/
theorem skeleton_pcOutput (hG : G.IsAcyclic) : (toDigraph (pcOutput I)).skeleton = G.skeleton :=
  (pcOutput_isPartialPattern hI hG).skeleton_eq

end Correctness

/-! ### The output is the pattern, given the completeness of the rules -/

/-- The completeness of the orientation rules, in the form of Meek (1995): in every partial
pattern for a finite acyclic graph `G` to which no rule applies, every compelled edge of `G` is
directed. This is a hypothesis of `Digraph.pcOutput_eq_pattern`; it holds for every finite
vertex type (`Digraph.meekComplete` in `CausalInference.Discovery.PatternCompleteness`). -/
def MeekComplete (V : Type*) [Fintype V] [DecidableEq V] : Prop :=
  ∀ G P : Digraph V, G.IsAcyclic → P.IsPartialPattern G → (∀ a b, ¬ MeekRule P a b) →
    ∀ u v, G.IsCompelled u v → P.IsArrow u v

/-- The number of arcs of a finset of pairs strictly decreases under a pass of the rules that
applies some rule. -/
theorem card_meekPassF_lt {A : Finset (V × V)} {a b : V} (h : MeekRule (toDigraph A) a b) :
    (meekPassF A).card < A.card := by
  refine card_lt_card ⟨filter_subset _ _, fun hsub => ?_⟩
  have hba : (b, a) ∈ A := h.isLine.2
  exact (mem_filter.1 (hsub hba)).2 h

/-- When no rule applies, a pass of the rules changes nothing. -/
theorem meekPassF_eq_self {A : Finset (V × V)} (h : ∀ a b, ¬ MeekRule (toDigraph A) a b) :
    meekPassF A = A :=
  filter_true_of_mem fun p _ => h p.2 p.1

/-- After `(card V) ^ 2` passes no rule applies any more. -/
theorem forall_not_meekRule_iterate (A : Finset (V × V)) :
    ∀ a b, ¬ MeekRule (toDigraph (meekPassF^[Fintype.card V ^ 2] A)) a b := by
  set N := Fintype.card V ^ 2
  by_contra hn
  push Not at hn
  have hnot : ∀ k ≤ N, ∃ a b, MeekRule (toDigraph (meekPassF^[k] A)) a b := by
    intro k hk
    by_contra hk'
    push Not at hk'
    have hfix : ∀ j, meekPassF^[k + j] A = meekPassF^[k] A := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [← add_assoc, Function.iterate_succ_apply', ih, meekPassF_eq_self hk']
    obtain ⟨a, b, h⟩ := hn
    have := hfix (N - k)
    rw [Nat.add_sub_cancel' hk] at this
    rw [this] at h
    exact hk' a b h
  have hdec : ∀ k ≤ N, (meekPassF^[k] A).card + k ≤ A.card := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨a, b, h⟩ := hnot k (Nat.le_of_succ_le hk)
      have := card_meekPassF_lt h
      rw [Function.iterate_succ_apply']
      have := ih (Nat.le_of_succ_le hk)
      omega
  obtain ⟨a, b, h⟩ := hnot N le_rfl
  have h1 := card_meekPassF_lt h
  have h2 := hdec N le_rfl
  have h3 : A.card ≤ N := by
    calc A.card ≤ (univ : Finset (V × V)).card := card_le_univ A
      _ = N := by rw [card_univ, Fintype.card_prod]; exact (sq _).symm
  omega

omit [Fintype V] [DecidableEq V] in
/-- A partial pattern whose directed edges are exactly the compelled edges is the pattern. -/
theorem IsPartialPattern.eq_pattern {P G : Digraph V} (hP : P.IsPartialPattern G)
    (hG : G.IsAcyclic) (h : ∀ u v, G.IsCompelled u v → P.IsArrow u v) : P = pattern G := by
  have hsk : ∀ u v, u ≠ v → (P.Adj u v ∨ P.Adj v u ↔ G.Adj u v ∨ G.Adj v u) := by
    intro u v huv
    have := congrArg (fun K : SimpleGraph V => K.Adj u v) hP.skeleton_eq
    simpa [skeleton_adj, huv] using this
  ext u v
  simp only [pattern]
  constructor
  · intro huv
    have hne : u ≠ v := fun e => hP.irrefl u (e ▸ huv)
    rcases (hsk u v hne).1 (Or.inl huv) with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', fun hc => (h v u hc).2 huv⟩
  · rintro (huv | ⟨hvu, hc⟩)
    · have hne := hG.ne_of_adj huv
      rcases (hsk u v hne).2 (Or.inl huv) with h' | h'
      · exact h'
      · by_contra hn
        exact hG.asymm huv (hP.isCompelled v u ⟨h', hn⟩).1
    · have hne := (hG.ne_of_adj hvu).symm
      rcases (hsk u v hne).2 (Or.inr hvu) with h' | h'
      · exact h'
      · by_contra hn
        exact hc (hP.isCompelled v u ⟨h', hn⟩)

/-- **The PC algorithm returns the pattern, given the completeness of the rules.** Under a
d-separation oracle of a finite acyclic graph `G`, and assuming the completeness of the
orientation rules (`Digraph.MeekComplete`, Meek 1995), the output of the PC algorithm is the
pattern of `G`. The completeness is proved as `Digraph.meekComplete`, and the unconditional form
is `Digraph.pcOutput_eq_pattern'`. -/
theorem pcOutput_eq_pattern {I : V → V → Finset V → Prop} [∀ x y S, Decidable (I x y S)]
    {G : Digraph V} (hI : ∀ x y S, I x y S ↔ G.DSep {x} {y} ↑S) (hG : G.IsAcyclic)
    (hMeek : MeekComplete V) : toDigraph (pcOutput I) = pattern G := by
  have hP := pcOutput_isPartialPattern hI hG
  exact hP.eq_pattern hG fun u v hc => hMeek G _ hG hP (forall_not_meekRule_iterate _) u v hc

end Digraph
