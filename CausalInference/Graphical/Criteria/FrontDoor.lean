/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Criteria.BackDoor

/-!
# Directed path interception and the front-door criterion

## Main definitions

* `Digraph.Intercepts G Z X Y`: every directed path from a vertex of `X` to a vertex of `Y`
  contains a vertex of `Z`. A path counts as intercepted when one of its endpoints is in `Z`,
  and the path of length zero at a vertex of `X ∩ Y` outside `Z` is not intercepted. This is the
  relation written `(X ↛ Y | Z)_G` in Pearl (2009), pp. 236 to 237.
* `Digraph.FrontDoor G X Y Z`: the front-door criterion (Pearl's Definition 3.3.3) in joint
  surgery form: `Z` intercepts all directed paths from `X` to `Y`;
  `(G.deleteOutgoing X).DSep X Z ∅`; and `(G.deleteOutgoing Z).DSep Z Y X`.

## Main results

* `Digraph.intercepts_iff_restrict`: interception as reachability in `G.restrict Zᶜ`.
* Properties of interception that mirror the axioms of Theorem 7.3.8 of Pearl (2009) and the
  axioms that Paz and Pearl (1994) add for directed graphs: left and right decomposition
  (`Digraph.Intercepts.mono_left`, `Digraph.Intercepts.mono_right`), strong union
  (`Digraph.Intercepts.mono_set`), weak right decomposition
  (`Digraph.Intercepts.weak_right_decomposition`), right and left intersection
  (`Digraph.Intercepts.right_intersection`, `Digraph.Intercepts.left_intersection`, which need
  disjointness hypotheses because an endpoint in the conditioning set counts as an
  interception), and transitivity (`Digraph.Intercepts.transitivity`). The extract of the
  book does not print transitivity and right decomposition; the forms here are the standard
  ones for path interception, re-derived.
* `Digraph.Intercepts.not_reflTransGen`: if `Z` intercepts all directed paths from `X` to `Y`
  and there is no directed path from `Z` to `Y`, then there is no directed path from `X` to `Y`
  (Pearl 2009, p. 237).
* `Digraph.notMem_descendantsOf_of_dSep`, `Digraph.FrontDoor.disjoint_descendantsOf`:
  condition (ii) alone rules out a directed path from `Z` back to `X`.
* `Digraph.frontDoor_singleton_iff`: for single vertices, conditions (ii) and (iii) in path
  form.
* Decidability, the canonical front-door graph (Pearl 2009, Figure 3.5, with the latent
  confounder as an explicit vertex) as a checked example, and non-examples.

## Joint surgery form

Conditions (ii) and (iii) are each a single d-separation test after removing the edges out of
the whole set `X`, respectively `Z`. Condition (iii) says that `Z` and `Y` are d-separated by
`X` once every edge out of every mediator is removed. For one treatment and one mediator this
is the path form of Definition 3.3.3 (`Digraph.frontDoor_singleton_iff`). For several mediators
it is weaker than the path form quantified over each mediator: a back-door path of one mediator
may leave through an edge out of another mediator, which the surgery removes
(`CausalInference.FrontDoorExamples.frontDoor_joint_not_pairwise`). The same holds for
condition (ii) with several treatments. The joint form is the one used by the front-door
adjustment theorem `SCM.effect_eq_sum_of_frontDoor`.

## References

* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 3.3.2,
  Definition 3.3.3 (Front-Door) and Figure 3.5; section 7.3, Theorem 7.3.8, pp. 236 to 237.
* A. Paz and J. Pearl (1994), *Axiomatic characterization of directed graphs*.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- `G.Intercepts Z X Y`: every directed path (of length zero or more) from a vertex of `X` to a
vertex of `Y` contains a vertex of `Z`. Equivalently, there is no `x ∈ X` outside `Z` from which
some `y ∈ Y` is reachable by a directed path all of whose vertices lie outside `Z`, that is, by
a directed path of `G.restrict Zᶜ` starting outside `Z`. -/
def Intercepts (G : Digraph V) (Z X Y : Set V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ∉ Z → ¬ ReflTransGen (G.restrict Zᶜ).Adj x y

/-- The front-door criterion (Pearl 2009, Definition 3.3.3) for `Z` relative to `(X, Y)`, in
joint surgery form:
(i) `Z` intercepts all directed paths from `X` to `Y`;
(ii) `X` and `Z` are d-separated by the empty set in the graph with the edges out of every
member of `X` removed;
(iii) `Z` and `Y` are d-separated by `X` in the graph with the edges out of every member of `Z`
removed.
For one treatment and one mediator, (ii) and (iii) say that no back-door path from `X` to `Z`
is unblocked and that `X` blocks every back-door path from `Z` to `Y`
(`frontDoor_singleton_iff`). For sets the surgery can remove a back-door path of one mediator
that leaves through another mediator before it is tested, so (iii) is weaker than the path
form quantified over each mediator. -/
def FrontDoor (G : Digraph V) (X Y Z : Set V) : Prop :=
  G.Intercepts Z X Y ∧ (G.deleteOutgoing X).DSep X Z ∅ ∧ (G.deleteOutgoing Z).DSep Z Y X

variable {G H : Digraph V} {X X' Y Y' Z Z' W S : Set V} {x y z u v : V}

/-! ### Paths avoiding a set -/

theorem intercepts_iff_restrict :
    G.Intercepts Z X Y ↔ ∀ x ∈ X, ∀ y ∈ Y, x ∉ Z → ¬ ReflTransGen (G.restrict Zᶜ).Adj x y :=
  Iff.rfl

/-- A directed path of `G` from `x` either avoids `S` entirely (`x ∉ S` and the path lies in
`G.restrict Sᶜ`) or reaches the end from some vertex of `S`. -/
theorem reflTransGen_restrict_or_exists (h : ReflTransGen G.Adj x y) :
    (x ∉ S ∧ ReflTransGen (G.restrict Sᶜ).Adj x y) ∨ ∃ s ∈ S, ReflTransGen G.Adj s y := by
  induction h using ReflTransGen.head_induction_on with
  | refl =>
    by_cases hy : y ∈ S
    · exact Or.inr ⟨y, hy, ReflTransGen.refl⟩
    · exact Or.inl ⟨hy, ReflTransGen.refl⟩
  | @head a b hab hby ih =>
    by_cases ha : a ∈ S
    · exact Or.inr ⟨a, ha, ReflTransGen.head hab hby⟩
    · rcases ih with ⟨hb, hpath⟩ | h
      · exact Or.inl ⟨ha, ReflTransGen.head ⟨hab, ha, hb⟩ hpath⟩
      · exact Or.inr h

/-- First hit: a directed path from `x` to a vertex of `S` has a prefix that ends at a vertex of
`S` and leaves no earlier vertex of `S`, that is, a path of `G.deleteOutgoing S`. -/
theorem exists_reflTransGen_deleteOutgoing (h : ReflTransGen G.Adj x y) (hy : y ∈ S) :
    ∃ s ∈ S, ReflTransGen (G.deleteOutgoing S).Adj x s := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨y, hy, ReflTransGen.refl⟩
  | @head a b hab _ ih =>
    by_cases ha : a ∈ S
    · exact ⟨a, ha, ReflTransGen.refl⟩
    · obtain ⟨s, hs, hpath⟩ := ih
      exact ⟨s, hs, ReflTransGen.head ⟨hab, ha⟩ hpath⟩

/-- Last hit: a directed path from a vertex of `S` has a suffix that starts at a vertex of `S`,
enters no later vertex of `S`, and starts either at the original start or at the head of an
edge of `G`. -/
theorem exists_reflTransGen_deleteIncoming (h : ReflTransGen G.Adj x y) (hx : x ∈ S) :
    ∃ s ∈ S, (s = x ∨ ∃ u, G.Adj u s) ∧ ReflTransGen (G.deleteIncoming S).Adj s y := by
  induction h with
  | refl => exact ⟨x, hx, Or.inl rfl, ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    by_cases hc : c ∈ S
    · exact ⟨c, hc, Or.inr ⟨b, hbc⟩, ReflTransGen.refl⟩
    · obtain ⟨s, hs, hsx, hpath⟩ := ih
      exact ⟨s, hs, hsx, hpath.tail ⟨hbc, hc⟩⟩

/-- A path of `G.deleteOutgoing S` ending outside `T ⊆ S` avoids `T` entirely. -/
theorem reflTransGen_restrict_of_deleteOutgoing {T : Set V}
    (h : ReflTransGen (G.deleteOutgoing S).Adj x y) (hy : y ∉ T) (hT : T ⊆ S) :
    x ∉ T ∧ ReflTransGen (G.restrict Tᶜ).Adj x y := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨hy, ReflTransGen.refl⟩
  | @head a b hab _ ih =>
    obtain ⟨hb, hpath⟩ := ih
    have ha : a ∉ T := fun h => hab.2 (hT h)
    exact ⟨ha, ReflTransGen.head ⟨hab.1, ha, hb⟩ hpath⟩

/-- A path of `G.deleteIncoming S` starting outside `T ⊆ S` avoids `T` entirely. -/
theorem reflTransGen_restrict_of_deleteIncoming {T : Set V}
    (h : ReflTransGen (G.deleteIncoming S).Adj x y) (hx : x ∉ T) (hT : T ⊆ S) :
    y ∉ T ∧ ReflTransGen (G.restrict Tᶜ).Adj x y := by
  induction h with
  | refl => exact ⟨hx, ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hpath⟩ := ih
    have hc : c ∉ T := fun h => hbc.2 (hT h)
    exact ⟨hc, hpath.tail ⟨hbc.1, hb, hc⟩⟩

theorem restrict_compl_restrict_compl :
    (G.restrict Zᶜ).restrict Wᶜ = G.restrict (Z ∪ W)ᶜ := by
  rw [restrict_restrict, Set.compl_union]

/-! ### Properties of interception -/

/-- With nothing to intercept, interception means that there is no directed path at all. -/
theorem intercepts_empty_iff :
    G.Intercepts ∅ X Y ↔ ∀ x ∈ X, ∀ y ∈ Y, ¬ ReflTransGen G.Adj x y := by
  simp [Intercepts]

/-- A set intercepts every directed path that starts inside it. -/
theorem intercepts_of_subset_left (h : X ⊆ Z) : G.Intercepts Z X Y :=
  fun _ hx _ _ hxZ => absurd (h hx) hxZ

/-- Interception forces `X ∩ Y ⊆ Z`, because of the paths of length zero. -/
theorem Intercepts.inter_subset (h : G.Intercepts Z X Y) : X ∩ Y ⊆ Z :=
  fun v ⟨hX, hY⟩ => by_contra fun hZ => h v hX v hY hZ ReflTransGen.refl

/-- Left decomposition. -/
theorem Intercepts.mono_left (hX : X' ⊆ X) (h : G.Intercepts Z X Y) : G.Intercepts Z X' Y :=
  fun x hx => h x (hX hx)

/-- Right decomposition. -/
theorem Intercepts.mono_right (hY : Y' ⊆ Y) (h : G.Intercepts Z X Y) : G.Intercepts Z X Y' :=
  fun x hx y hy => h x hx y (hY hy)

theorem intercepts_union_left :
    G.Intercepts Z (X ∪ X') Y ↔ G.Intercepts Z X Y ∧ G.Intercepts Z X' Y :=
  ⟨fun h => ⟨h.mono_left Set.subset_union_left, h.mono_left Set.subset_union_right⟩,
    fun ⟨h, h'⟩ x hx => hx.elim (h x) (h' x)⟩

theorem intercepts_union_right :
    G.Intercepts Z X (Y ∪ Y') ↔ G.Intercepts Z X Y ∧ G.Intercepts Z X Y' :=
  ⟨fun h => ⟨h.mono_right Set.subset_union_left, h.mono_right Set.subset_union_right⟩,
    fun ⟨h, h'⟩ x hx y hy => hy.elim (h x hx y) (h' x hx y)⟩

/-- Strong union: enlarging the intercepting set preserves interception. -/
theorem Intercepts.mono_set (hZ : Z ⊆ Z') (h : G.Intercepts Z X Y) : G.Intercepts Z' X Y :=
  fun x hx y hy hxZ hpath => h x hx y hy (fun h => hxZ (hZ h))
    (ReflTransGen.mono (fun _ _ huv => ⟨huv.1, fun h => huv.2.1 (hZ h),
      fun h => huv.2.2 (hZ h)⟩) _ _ hpath)

/-- Weak right decomposition (the form of Theorem 7.3.8 adopted after Bonet 2001). For path
interception it already follows from right decomposition. -/
theorem Intercepts.weak_right_decomposition (h : G.Intercepts Z X (Y ∪ W))
    (_ : G.Intercepts (Z ∪ W) X Y) : G.Intercepts Z X Y :=
  h.mono_right Set.subset_union_left

/-- Right intersection: if `Z ∪ W` intercepts the paths from `X` to `Y` and `Z ∪ Y` intercepts
those from `X` to `W`, then `Z` intercepts those from `X` to `Y ∪ W`. The hypothesis that `Y`
and `W` are disjoint is needed: with `Y = W = {t}` and an edge `x → t`, both hypotheses hold
because the endpoint `t` is in the intercepting set, while the conclusion fails. -/
theorem Intercepts.right_intersection (hYW : Disjoint Y W) (hY : G.Intercepts (Z ∪ W) X Y)
    (hW : G.Intercepts (Z ∪ Y) X W) : G.Intercepts Z X (Y ∪ W) := by
  intro x hx t ht hxZ hpath
  obtain ⟨s, hs, hxs⟩ := exists_reflTransGen_deleteOutgoing hpath ht
  rcases hs with hsY | hsW
  · obtain ⟨hxW, hp⟩ := reflTransGen_restrict_of_deleteOutgoing hxs
      (Set.disjoint_left.1 hYW hsY) Set.subset_union_right
    rw [restrict_compl_restrict_compl] at hp
    exact hY x hx s hsY (fun h => h.elim hxZ hxW) hp
  · obtain ⟨hxY, hp⟩ := reflTransGen_restrict_of_deleteOutgoing hxs
      (Set.disjoint_right.1 hYW hsW) Set.subset_union_left
    rw [restrict_compl_restrict_compl] at hp
    exact hW x hx s hsW (fun h => h.elim hxZ hxY) hp

/-- Left intersection: if `Z ∪ W` intercepts the paths from `X` to `Y` and `Z ∪ X` intercepts
those from `W` to `Y`, then `Z` intercepts those from `X ∪ W` to `Y`. The hypothesis that `X`
and `W` are disjoint is needed: with `X = W = {v}` and an edge `v → y`, both hypotheses hold
because the start `v` is in the intercepting set, while the conclusion fails. -/
theorem Intercepts.left_intersection (hXW : Disjoint X W) (hX : G.Intercepts (Z ∪ W) X Y)
    (hW : G.Intercepts (Z ∪ X) W Y) : G.Intercepts Z (X ∪ W) Y := by
  intro x hx y hy hxZ hpath
  obtain ⟨s, hs, hsx, hsy⟩ := exists_reflTransGen_deleteIncoming hpath hx
  have hsZ : s ∉ Z := by
    rcases hsx with rfl | ⟨u, hus⟩
    · exact hxZ
    · exact hus.2.2
  rcases hs with hsX | hsW
  · obtain ⟨-, hp⟩ := reflTransGen_restrict_of_deleteIncoming hsy
      (Set.disjoint_left.1 hXW hsX) Set.subset_union_right
    rw [restrict_compl_restrict_compl] at hp
    exact hX s hsX y hy (fun h => h.elim hsZ (Set.disjoint_left.1 hXW hsX)) hp
  · obtain ⟨-, hp⟩ := reflTransGen_restrict_of_deleteIncoming hsy
      (Set.disjoint_right.1 hXW hsW) Set.subset_union_left
    rw [restrict_compl_restrict_compl] at hp
    exact hW s hsW y hy (fun h => h.elim hsZ (Set.disjoint_right.1 hXW hsW)) hp

/-- Transitivity, in the form of the separation axiom for path interception: if `Z` intercepts
all directed paths from `X` to `Y`, then for every vertex `w`, either `Z` intercepts all directed
paths from `X` to `w` or all directed paths from `w` to `Y`. -/
theorem Intercepts.transitivity (h : G.Intercepts Z X Y) (w : V) :
    G.Intercepts Z X {w} ∨ G.Intercepts Z {w} Y := by
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.1 hcon
  apply h1
  intro x hx w' hw' hxZ hxw
  rw [Set.mem_singleton_iff] at hw'
  subst hw'
  apply h2
  intro w'' hw'' y hy _ hwy
  rw [Set.mem_singleton_iff] at hw''
  subst hw''
  exact h x hx y hy hxZ (hxw.trans hwy)

/-- Pearl (2009), p. 237: if `Z` intercepts all directed paths from `X` to `Y` and there is no
directed path from `Z` to `Y`, then there is no directed path from `X` to `Y`. -/
theorem Intercepts.not_reflTransGen (h : G.Intercepts Z X Y)
    (hZ : ∀ z ∈ Z, ∀ y ∈ Y, ¬ ReflTransGen G.Adj z y) (hx : x ∈ X) (hy : y ∈ Y) :
    ¬ ReflTransGen G.Adj x y := by
  intro hpath
  rcases reflTransGen_restrict_or_exists (S := Z) hpath with ⟨hxZ, hp⟩ | ⟨z, hz, hzy⟩
  · exact h x hx y hy hxZ hp
  · exact hZ z hz y hy hzy

/-! ### The front-door criterion -/

/-- Condition (ii) of the front-door criterion alone rules out a directed path from `Z` to a
member of `X`: such a path, cut at its first vertex in `X`, would be a back-door path from `X`
to `Z` that is active given the empty set. -/
theorem notMem_descendantsOf_of_dSep (h : (G.deleteOutgoing X).DSep X Z ∅) {u : V}
    (hu : u ∈ X) : u ∉ G.descendantsOf Z := by
  rintro ⟨s, hs, hsu⟩
  obtain ⟨t, ht, hst⟩ := exists_reflTransGen_deleteOutgoing hsu hu
  have hs' : s ∉ (G.deleteOutgoing X).ancestorsOf ∅ := fun ⟨_, hw, _⟩ => hw
  obtain ⟨c, hc⟩ := exists_reflTransGen_bayesBall_of_reflTransGen hst hs' false
  exact h (DConn.symm ⟨s, hs, t, ht, Set.notMem_empty s, Set.notMem_empty t, c, hc⟩)

/-- Under the front-door criterion no treatment vertex is a descendant of a mediator. -/
theorem FrontDoor.notMem_descendantsOf_mediator (h : G.FrontDoor X Y Z) {u : V} (hu : u ∈ X) :
    u ∉ G.descendantsOf Z :=
  notMem_descendantsOf_of_dSep h.2.1 hu

/-- Under the front-door criterion the treatment set is disjoint from the descendants of the
mediators. -/
theorem FrontDoor.disjoint_descendantsOf (h : G.FrontDoor X Y Z) :
    Disjoint X (G.descendantsOf Z) :=
  Set.disjoint_left.2 fun _ hu => h.notMem_descendantsOf_mediator hu

/-- For single vertices, Pearl's conditions (ii) and (iii) in path form. Condition (ii): no
simple path from `x` to `z` that starts with an arrow into `x` is active given the empty set.
Condition (iii): every simple path from `z` to `y` that starts with an arrow into `z` is
blocked by `x`. Either form of (ii) implies that `x` is not a descendant of `z`
(`notMem_descendantsOf_of_dSep`), which the path form of (iii) needs. -/
theorem frontDoor_singleton_iff (hxz : x ≠ z) (hzy : z ≠ y) :
    G.FrontDoor {x} {y} {z} ↔ G.Intercepts {z} {x} {y} ∧ ¬ G.OpenBackDoorPath ∅ x z ∧
      ¬ G.OpenBackDoorPath {x} z y := by
  have hii := deleteOutgoing_dSep_singleton_iff (G := G) (Z := ∅) hxz
    (fun _ h => (Set.notMem_empty _ h).elim)
  have hiii (h2 : (G.deleteOutgoing {x}).DSep {x} {z} ∅) :=
    deleteOutgoing_dSep_singleton_iff (G := G) (Z := {x}) hzy (fun v hv => by
      rw [Set.mem_singleton_iff] at hv
      exact hv ▸ notMem_descendantsOf_of_dSep h2 rfl)
  unfold FrontDoor
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, hii.1 h2, (hiii h2).1 h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, hii.2 h2, (hiii (hii.2 h2)).2 h3⟩

section Decidable

variable (G : Digraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance decidableIntercepts (Z X Y : Set V) [DecidablePred (· ∈ Z)] [DecidablePred (· ∈ X)]
    [DecidablePred (· ∈ Y)] : Decidable (G.Intercepts Z X Y) :=
  inferInstanceAs (Decidable (∀ x, x ∈ X → ∀ y, y ∈ Y → _))

instance decidableFrontDoor (X Y Z : Set V) [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)]
    [DecidablePred (· ∈ Z)] : Decidable (G.FrontDoor X Y Z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Decidable

end Digraph

namespace CausalInference.FrontDoorExamples

open Criteria

/-- Pearl (2009), Figure 3.5, with the latent confounder as an explicit vertex: `U → X`,
`U → Y`, `X → Z`, `Z → Y`, where `X = 0`, `Z = 1`, `Y = 2`, `U = 3` (smoking, tar, cancer, and
the genotype in section 3.3.3). -/
abbrev pearlFig35 : Digraph (Fin 4) := ofEdges [(3, 0), (3, 2), (0, 1), (1, 2)]

example : pearlFig35.IsAcyclic := by decide +kernel
example : pearlFig35.FrontDoor {0} {2} {1} := by decide +kernel
-- The effect is not identified by adjustment for observed variables: neither `∅` nor `{Z}`
-- satisfies the back-door criterion, only the latent `{U}` does.
example : ¬ pearlFig35.BackDoor {0} {2} ∅ := by decide +kernel
example : ¬ pearlFig35.BackDoor {0} {2} {1} := by decide +kernel
example : pearlFig35.BackDoor {0} {2} {3} := by decide +kernel

/-- Non-example: Figure 3.5 with a direct edge `X → Y`, so `Z` no longer intercepts every
directed path from `X` to `Y` (condition (i) fails). -/
abbrev frontDoorDirect : Digraph (Fin 4) := ofEdges [(3, 0), (3, 2), (0, 1), (1, 2), (0, 2)]

example : ¬ frontDoorDirect.Intercepts {1} {0} {2} := by decide +kernel
example : ¬ frontDoorDirect.FrontDoor {0} {2} {1} := by decide +kernel

/-- Non-example: Figure 3.5 with an edge `U → Z`, which opens the back-door path
`X ← U → Z` (condition (ii) fails). -/
abbrev frontDoorConfounded : Digraph (Fin 4) :=
  ofEdges [(3, 0), (3, 2), (0, 1), (1, 2), (3, 1)]

example : frontDoorConfounded.Intercepts {1} {0} {2} := by decide +kernel
example : ¬ (frontDoorConfounded.deleteOutgoing {0}).DSep {0} {1} ∅ := by decide +kernel
example : ¬ frontDoorConfounded.FrontDoor {0} {2} {1} := by decide +kernel

/-- Non-example: Figure 3.5 with a second latent `U' → Z`, `U' → Y` (`U' = 4`); `X` does not
block the back-door path `Z ← U' → Y` (condition (iii) fails). -/
abbrev frontDoorMediatorConfounded : Digraph (Fin 5) :=
  ofEdges [(3, 0), (3, 2), (0, 1), (1, 2), (4, 1), (4, 2)]

example : (frontDoorMediatorConfounded.deleteOutgoing {0}).DSep {0} {1} ∅ := by decide +kernel
example : ¬ (frontDoorMediatorConfounded.deleteOutgoing {1}).DSep {1} {2} {0} := by decide +kernel
example : ¬ frontDoorMediatorConfounded.FrontDoor {0} {2} {1} := by decide +kernel

-- Interception on a chain `0 → 1 → 2`: the middle vertex intercepts, the empty set does not,
-- and an endpoint in the intercepting set counts as an interception.
example : GraphExamples.chain.Intercepts {1} {0} {2} := by decide +kernel
example : ¬ GraphExamples.chain.Intercepts ∅ {0} {2} := by decide +kernel
example : GraphExamples.chain.Intercepts {2} {0} {2} := by decide +kernel

/-- The joint form of condition (iii) differs from the path form quantified over each mediator:
`X → m₂`, `m₂ → m₁`, `m₁ → Y`, `m₂ → Y`, with `X = 0`, `m₁ = 1`, `m₂ = 2`, `Y = 3`. The set
`{m₁, m₂}` satisfies `FrontDoor`, yet the back-door path `m₁ ← m₂ → Y` from the mediator `m₁`
is open given `X`: removing the edges out of both mediators deletes it. -/
theorem frontDoor_joint_not_pairwise :
    (ofEdges (n := 4) [(0, 2), (2, 1), (1, 3), (2, 3)]).FrontDoor {0} {3} {1, 2} ∧
      (ofEdges (n := 4) [(0, 2), (2, 1), (1, 3), (2, 3)]).OpenBackDoorPath {0} 1 3 := by
  refine ⟨by decide +kernel, 2, [2, 3], by decide, by simp, ?_, by decide⟩
  exact .fwd (by decide) (by simp) (.nil (by simp))

end CausalInference.FrontDoorExamples
