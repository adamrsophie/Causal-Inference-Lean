/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Closure
public import CausalInference.Graphical.DSeparationDecide

/-!
# The back-door criterion

## Main definitions

* `Digraph.BackDoor G X Y Z`: the set `Z` satisfies the back-door criterion relative to
  `(X, Y)`: no member of `Z` is in the inclusive descendant closure of `X`, and `X` and `Y` are
  d-separated by `Z` in `G.deleteOutgoing X`, the graph with every edge out of `X` removed.
* `Digraph.OpenBackDoorPath G Z x y`: there is a simple path from `x` to `y` in `G` that starts
  with an edge into `x` and is active given `Z`.
* `Digraph.BackDoorPairwise G X Y Z`: Pearl's Definition 3.3.1 extended to sets pairwise, in path
  form: no member of `Z` is a descendant of `X`, and for every `x ∈ X` and `y ∈ Y`, `Z` blocks
  every simple path from `x` to `y` that starts with an arrow into `x`.
* `Digraph.BackDoorAdjustment G X Y Z`: the criterion in the setting of the adjustment formula:
  `Digraph.BackDoor G X Y Z` and `Y` disjoint from `Z`.

## Main results

* `Digraph.backDoor_singleton_iff`: for a single treatment `x` and outcome `y ≠ x`, the
  surgery form of condition (ii) is equivalent to the path form of Pearl's Definition 3.3.1,
  "`Z` blocks every path between `x` and `y` that contains an arrow into `x`", provided
  condition (i) holds. This is the single d-separation test of Pearl (2009), footnote 5 on
  p. 79 and equation (3.37).
* `Digraph.BackDoorPairwise.backDoor`: for disjoint `X` and `Y`, the pairwise path form implies
  the joint surgery form; `Digraph.backDoorPairwise_singleton_iff`: they agree for a single
  treatment and outcome. The converse fails for several treatments
  (`CausalInference.BackDoorExamples.backDoor_not_pairwise_fork`,
  `CausalInference.BackDoorExamples.backDoor_not_pairwise_common_cause`).
* `Digraph.IsAcyclic.backDoor_parents`: in a DAG the parents of `x` satisfy the criterion
  relative to `(x, y)` for every `y ≠ x`; `Digraph.IsAcyclic.backDoorAdjustment_parents` adds
  `y ∉ G.parents x` and gives the adjustment-facing form.
* `Digraph.BackDoor.insert_covariate`,
  `Digraph.BackDoor.insert_covariate_of_mem_ancestorsOf`: sufficient conditions under which
  adding a nondescendant `w` of `X` to an admissible set keeps it admissible (the M-bias
  example shows that some condition is needed).
* `Digraph.backDoor_empty_of_parents_eq_empty`: if no member of `X` has a parent, the empty set
  satisfies the criterion relative to `(X, Y)` for every `Y` disjoint from `X`.
* Decidability, and the examples: Pearl (2009) Figure 3.4, What If Figures 7.1, 7.4 (M-bias),
  7.5 and 7.6, and the Primer's Figures 3.6 and 3.7, all checked by `decide`.

## The definition for sets of treatments

Pearl states the criterion for a pair of vertices and extends it to sets pairwise. The
definition `Digraph.BackDoor` is instead the joint surgery form: the single test
`(G.deleteOutgoing X).DSep X Y Z` for the whole set `X`. For several treatments it is not
Pearl's pairwise Definition 3.3.1: a back-door path of `x₁` may leave through an edge out of
another treatment `x₂`, and the surgery removes that edge. Two examples: with `x₂ → x₁`,
`x₂ → y`, the empty set passes the joint test for `X = {x₁, x₂}` while the path
`x₁ ← x₂ → y` is open; with `a → x₁`, `a → x₂`, `x₂ → y`, the empty set passes the joint test
while `x₁ ← a → x₂ → y` is open. In both, the joint intervention is identified by the
adjustment formula with the empty set, `P(y | do(x₁, x₂)) = P(y | x₁, x₂)`: the joint surgery
form is the one that licenses the adjustment formula for the joint intervention (it is the form
of Rule 2 of the do-calculus, and the form that `SCM.effect_eq_sum_of_backDoor` consumes). The
pairwise form `Digraph.BackDoorPairwise` implies it when `X` and `Y` are disjoint, and the two
agree for a single treatment.

Condition (i) uses the inclusive descendant closure, so it also forces `Z` and `X` to be
disjoint, as Pearl assumes.

## References

* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 3.3.1,
  Definition 3.3.1 (Back-Door) and Figure 3.4.
* J. Pearl, M. Glymour, N. P. Jewell (2016), *Causal Inference in Statistics: A Primer*,
  section 3.3, Definition 3.3.1 and Figures 3.6, 3.7.
* M. A. Hernán and J. M. Robins (2020), *Causal Inference: What If*, section 7.3 and
  Figures 7.1, 7.4, 7.5, 7.6.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- The back-door criterion in joint surgery form for the sets `X`, `Y`, `Z`: (i) no member of
`Z` is a descendant of `X` (in the inclusive sense, so `Z` and `X` are also disjoint), and
(ii) `X` and `Y` are d-separated by `Z` in `G.deleteOutgoing X`, the graph in which every edge
out of every member of `X` is removed. For a single treatment this is Pearl's Definition 3.3.1
(`backDoor_singleton_iff`). For several treatments it is weaker than Pearl's pairwise extension
(`BackDoorPairwise`), and it is the form that licenses the adjustment formula for the joint
intervention. It allows `Y` to meet `Z`; `BackDoorAdjustment` excludes that. -/
def BackDoor (G : Digraph V) (X Y Z : Set V) : Prop :=
  (∀ z ∈ Z, z ∉ G.descendantsOf X) ∧ (G.deleteOutgoing X).DSep X Y Z

/-- `G.OpenBackDoorPath Z x y`: there is a simple path `x ← v ⋯ y` in `G`, starting with an
edge into `x`, that is active given `Z`. It is recorded as an edge `v → x`, the condition
`x ∉ Z` on the first vertex, an active trail from `v` to `y` (entered at `v` through a tail, as
the edge `v → x` leaves `v`), and the requirement that `x` followed by that trail has no repeated
vertex. -/
def OpenBackDoorPath (G : Digraph V) (Z : Set V) (x y : V) : Prop :=
  ∃ v l, G.Adj v x ∧ x ∉ Z ∧ G.ActiveTrail Z false v y l ∧ (x :: l).Nodup

/-- Pearl's back-door criterion (Definition 3.3.1) extended to sets pairwise, in path form: no
member of `Z` is a descendant of `X`, and for every `x ∈ X` and `y ∈ Y`, every simple path from
`x` to `y` that starts with an arrow into `x` is blocked by `Z`. -/
def BackDoorPairwise (G : Digraph V) (X Y Z : Set V) : Prop :=
  (∀ z ∈ Z, z ∉ G.descendantsOf X) ∧ ∀ x ∈ X, ∀ y ∈ Y, ¬ G.OpenBackDoorPath Z x y

/-- The back-door criterion in the setting of the adjustment formula (Pearl 2009,
Theorem 3.3.2): `Z` satisfies `BackDoor G X Y Z`, and the outcome `Y` is disjoint from `Z`.
Without disjointness the criterion can hold for the degenerate reason that an outcome in the
conditioning set is blocked as an endpoint (for `y → x`, `BackDoor {x} {y} {y}` holds). The
treatment `X` is disjoint from `Z` and from `Y` by `BackDoor` itself. -/
def BackDoorAdjustment (G : Digraph V) (X Y Z : Set V) : Prop :=
  G.BackDoor X Y Z ∧ Disjoint Y Z

variable {G H : Digraph V} {X Y Z : Set V} {x y u w : V} {a : Bool} {l : List V}

/-! ### Active trails under edge deletion -/

/-- An active trail in a subgraph is an active trail in the larger graph. -/
theorem ActiveTrail.mono (hHG : H ≤ G) (p : H.ActiveTrail Z a u w l) :
    G.ActiveTrail Z a u w l := by
  induction p with
  | nil hv => exact .nil hv
  | fwd h hu _ ih => exact .fwd (hHG h) hu ih
  | bwd h hu _ ih => exact .bwd (hHG h) hu ih
  | collider h hu _ ih => exact .collider (hHG h) (ancestorsOf_mono_graph hHG Z hu) ih

/-- The first vertex of an active trail is the head of its vertex list. -/
theorem ActiveTrail.exists_eq_cons (p : G.ActiveTrail Z a u w l) : ∃ l', l = u :: l' := by
  cases p <;> exact ⟨_, rfl⟩

/-- The first vertex of an active trail belongs to its vertex list. -/
theorem ActiveTrail.head_mem (p : G.ActiveTrail Z a u w l) : u ∈ l := by
  obtain ⟨l', rfl⟩ := p.exists_eq_cons
  exact List.mem_cons_self

/-- An active trail of `G` that avoids `X` is an active trail of `G.deleteOutgoing X`, provided
deleting the edges out of `X` does not shrink the ancestral closure of `Z`. -/
theorem ActiveTrail.deleteOutgoing (p : G.ActiveTrail Z a u w l) (hl : ∀ v ∈ l, v ∉ X)
    (hZ : G.ancestorsOf Z ⊆ (G.deleteOutgoing X).ancestorsOf Z) :
    (G.deleteOutgoing X).ActiveTrail Z a u w l := by
  induction p with
  | nil hv => exact .nil hv
  | fwd h hu q ih =>
    exact .fwd ⟨h, hl _ List.mem_cons_self⟩ hu (ih fun v hv => hl v (List.mem_cons_of_mem _ hv))
  | bwd h hu q ih =>
    exact .bwd ⟨h, hl _ (List.mem_cons_of_mem _ q.head_mem)⟩ hu
      (ih fun v hv => hl v (List.mem_cons_of_mem _ hv))
  | collider h hu q ih =>
    exact .collider ⟨h, hl _ (List.mem_cons_of_mem _ q.head_mem)⟩ (hZ hu)
      (ih fun v hv => hl v (List.mem_cons_of_mem _ hv))

/-- If no member of `Z` is a descendant of `X`, then deleting the edges out of `X` does not
change the ancestral closure of `Z`. -/
theorem ancestorsOf_deleteOutgoing_eq_of_forall (hZ : ∀ z ∈ Z, z ∉ G.descendantsOf X) :
    (G.deleteOutgoing X).ancestorsOf Z = G.ancestorsOf Z := by
  refine ancestorsOf_deleteOutgoing_of_disjoint (Set.disjoint_left.2 ?_)
  rintro v hv ⟨z, hz, hvz⟩
  exact hZ z hz ⟨v, hv, hvz⟩

/-! ### The path form for a single treatment -/

/-- The single d-separation test for back-door admissibility (Pearl 2009, footnote 5 on p. 79
and equation (3.37)). For a treatment `x`, an outcome `y ≠ x`, and a set `Z` without descendants
of `x` (condition (i)), `x` and `y` are d-separated by `Z` in `G.deleteOutgoing {x}` exactly when
`Z` blocks every simple path between `x` and `y` in `G` that starts with an arrow into `x`. -/
theorem deleteOutgoing_dSep_singleton_iff (hxy : x ≠ y)
    (hZ : ∀ z ∈ Z, z ∉ G.descendantsOf {x}) :
    (G.deleteOutgoing {x}).DSep {x} {y} Z ↔ ¬ G.OpenBackDoorPath Z x y := by
  constructor
  · rintro hsep ⟨v, l, hvx, hxZ, hl, hnd⟩
    have hxl : x ∉ l := (List.nodup_cons.1 hnd).1
    have hl' : (G.deleteOutgoing {x}).ActiveTrail Z false v y l :=
      hl.deleteOutgoing (fun t ht htx => hxl (htx ▸ ht))
        (ancestorsOf_deleteOutgoing_eq_of_forall hZ).symm.subset
    have hvx' : (G.deleteOutgoing {x}).Adj v x := by
      refine ⟨hvx, fun hv => hxl ?_⟩
      rw [Set.mem_singleton_iff] at hv
      exact hv ▸ hl.head_mem
    exact hsep (dConn_iff_dConnTrail.2 ⟨x, rfl, y, rfl, _, .bwd hvx' hxZ hl'⟩)
  · rintro hopen hconn
    obtain ⟨x', hx', y', hy', l, hl, hnd⟩ := dConn_iff_dConnPath.1 hconn
    rw [Set.mem_singleton_iff] at hx' hy'
    subst hx' hy'
    cases hl with
    | nil _ => exact hxy rfl
    | fwd h _ _ => exact h.2 rfl
    | bwd h hu p => exact hopen ⟨_, _, h.1, hu, p.mono deleteOutgoing_le, hnd⟩

/-- For a single treatment and an outcome `y ≠ x`, the back-door criterion in surgery form is
Pearl's Definition 3.3.1: no member of `Z` is a descendant of `x`, and `Z` blocks every simple
path between `x` and `y` that contains an arrow into `x`. -/
theorem backDoor_singleton_iff (hxy : x ≠ y) :
    G.BackDoor {x} {y} Z ↔ (∀ z ∈ Z, z ∉ G.descendantsOf {x}) ∧ ¬ G.OpenBackDoorPath Z x y :=
  and_congr_right fun hZ => deleteOutgoing_dSep_singleton_iff hxy hZ

/-! ### The pairwise form -/

/-- For disjoint `X` and `Y`, Pearl's pairwise criterion implies the joint surgery form: a path
that is active in `G.deleteOutgoing X` and leaves its first vertex `x ∈ X` must do so through an
edge into `x`, and it is active in `G` as well. Disjointness is needed: for `x ∈ X ∩ Y` outside
`Z` the pairwise condition holds vacuously, while `x` is d-connected to itself. The converse
fails for several treatments (`CausalInference.BackDoorExamples.backDoor_not_pairwise_fork`). -/
theorem BackDoorPairwise.backDoor (h : G.BackDoorPairwise X Y Z) (hXY : Disjoint X Y) :
    G.BackDoor X Y Z := by
  refine ⟨h.1, fun hconn => ?_⟩
  obtain ⟨x, hx, y, hy, l, hl, hnd⟩ := dConn_iff_dConnPath.1 hconn
  cases hl with
  | nil _ => exact Set.disjoint_left.1 hXY hx hy
  | fwd hadj _ _ => exact hadj.2 hx
  | bwd hadj hu p => exact h.2 x hx y hy ⟨_, _, hadj.1, hu, p.mono deleteOutgoing_le, hnd⟩

/-- For a single treatment and outcome, the pairwise and the joint forms agree. -/
theorem backDoorPairwise_singleton_iff (hxy : x ≠ y) :
    G.BackDoorPairwise {x} {y} Z ↔ G.BackDoor {x} {y} Z := by
  rw [backDoor_singleton_iff hxy, BackDoorPairwise]
  simp only [Set.mem_singleton_iff, forall_eq]

/-! ### Two admissible sets -/

/-- In a DAG the parents of `x` satisfy the back-door criterion relative to `(x, y)` for every
`y ≠ x` (Pearl 2009, Theorem 3.2.2, read graphically; the Primer notes that the parents of `X`
always satisfy the criterion). The hypothesis `y ≠ x` cannot be dropped: a vertex outside the
conditioning set is never d-separated from itself. A parent `y` of `x` is allowed; it then lies
in the conditioning set and the separation holds only because an endpoint is conditioned on, so
that case is outside the setting of the adjustment formula;
`IsAcyclic.backDoorAdjustment_parents` excludes it. -/
theorem IsAcyclic.backDoor_parents (hG : G.IsAcyclic) (hxy : x ≠ y) :
    G.BackDoor {x} {y} (G.parents x) := by
  refine ⟨fun z hz ⟨s, hs, hsz⟩ => ?_, ?_⟩
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hG s (TransGen.tail' hsz hz)
  · have hG' := hG.deleteOutgoing (X := {x})
    have h := hG'.dSep_nondescendants_parents x
    rw [descendantsOf_deleteOutgoing_of_subset subset_rfl, parents_deleteOutgoing,
      Set.sdiff_singleton_eq_self (fun hx => hG.irrefl x hx)] at h
    exact h.mono_right (Set.singleton_subset_iff.2 (Set.mem_compl_singleton_iff.2 hxy.symm))

/-- The adjustment-facing form of `IsAcyclic.backDoor_parents`: in a DAG the parents of `x`
satisfy `BackDoorAdjustment` relative to `(x, y)` for every `y ≠ x` that is not a parent
of `x`. -/
theorem IsAcyclic.backDoorAdjustment_parents (hG : G.IsAcyclic) (hxy : x ≠ y)
    (hy : y ∉ G.parents x) : G.BackDoorAdjustment {x} {y} (G.parents x) :=
  ⟨hG.backDoor_parents hxy, Set.disjoint_singleton_left.2 hy⟩

/-- If no member of `X` has a parent, the empty set satisfies the back-door criterion relative
to `(X, Y)` for every `Y` disjoint from `X`: after the edges out of `X` are removed, every
member of `X` is isolated. Disjointness is needed, since a vertex is d-connected to itself. -/
theorem backDoor_empty_of_parents_eq_empty (hX : ∀ x ∈ X, G.parents x = ∅)
    (hXY : Disjoint X Y) : G.BackDoor X Y ∅ := by
  refine ⟨fun _ hz => hz.elim, ?_⟩
  rintro ⟨x, hx, y, hy, -, -, b, h⟩
  rcases h.cases_head with h | ⟨⟨w, c⟩, hstep, -⟩
  · obtain ⟨rfl, -⟩ := Prod.mk.inj h
    exact Set.disjoint_left.1 hXY hx hy
  · cases c
    · have hwx := (bayesBall_adj_false_false.1 hstep).1.1
      have : w ∈ G.parents x := hwx
      rw [hX x hx] at this
      exact this
    · exact (bayesBall_adj_true.1 hstep).1.2 hx

/-! ### Adding a covariate -/

/-- Shrinking the conditioning set from `insert w Z` to `Z` keeps a trail active when every
vertex of the trail that is an ancestor of `w` is an ancestor of `Z`. -/
theorem ActiveTrail.of_insert (p : G.ActiveTrail (insert w Z) a u x l)
    (h : ∀ t ∈ l, t ∈ G.ancestorsOf {w} → t ∈ G.ancestorsOf Z) : G.ActiveTrail Z a u x l := by
  induction p with
  | nil hv => exact .nil fun h' => hv (Set.mem_insert_of_mem _ h')
  | fwd hadj hu _ ih =>
    exact .fwd hadj (fun h' => hu (Set.mem_insert_of_mem _ h'))
      (ih fun t ht => h t (List.mem_cons_of_mem _ ht))
  | bwd hadj hu _ ih =>
    exact .bwd hadj (fun h' => hu (Set.mem_insert_of_mem _ h'))
      (ih fun t ht => h t (List.mem_cons_of_mem _ ht))
  | collider hadj hu _ ih =>
    refine .collider hadj ?_ (ih fun t ht => h t (List.mem_cons_of_mem _ ht))
    obtain ⟨s, hs, hus⟩ := hu
    rcases hs with rfl | hs
    · exact h _ List.mem_cons_self ⟨_, rfl, hus⟩
    · exact ⟨s, hs, hus⟩

/-- Adding a covariate `w` that is not a descendant of `X` preserves the back-door criterion,
provided that, in `H = G.deleteOutgoing X`, every vertex of a simple path from `X` to `Y` that
is active given `Z ∪ {w}` and is an ancestor of `w` is already an ancestor of `Z`. Then such a
path is active given `Z` as well, so there is none. The sufficient condition of the M-bias
discussion asks this only of the colliders of the path; the hypothesis here asks it of every
vertex of the path, so it is stronger. -/
theorem BackDoor.insert_covariate (h : G.BackDoor X Y Z) (hwX : w ∉ G.descendantsOf X)
    (hw : ∀ x ∈ X, ∀ y ∈ Y, ∀ l, (G.deleteOutgoing X).ActiveTrail (insert w Z) false x y l →
      l.Nodup → ∀ t ∈ l, t ∈ (G.deleteOutgoing X).ancestorsOf {w} →
        t ∈ (G.deleteOutgoing X).ancestorsOf Z) :
    G.BackDoor X Y (insert w Z) := by
  refine ⟨fun z hz => ?_, fun hc => ?_⟩
  · rcases hz with rfl | hz
    · exact hwX
    · exact h.1 z hz
  · obtain ⟨x, hx, y, hy, l, hl, hnd⟩ := dConn_iff_dConnPath.1 hc
    exact h.2 (dConn_iff_dConnTrail.2 ⟨x, hx, y, hy, l, hl.of_insert (hw x hx y hy l hl hnd)⟩)

/-- Adding a covariate `w` that is not a descendant of `X` and is an ancestor of `Z` in
`G.deleteOutgoing X` preserves the back-door criterion. -/
theorem BackDoor.insert_covariate_of_mem_ancestorsOf (h : G.BackDoor X Y Z)
    (hwX : w ∉ G.descendantsOf X) (hw : w ∈ (G.deleteOutgoing X).ancestorsOf Z) :
    G.BackDoor X Y (insert w Z) := by
  refine h.insert_covariate hwX fun _ _ _ _ _ _ _ t _ ⟨s, hs, hts⟩ => ?_
  rw [Set.mem_singleton_iff] at hs
  subst hs
  obtain ⟨z, hz, hsz⟩ := hw
  exact ⟨z, hz, hts.trans hsz⟩

section Decidable

variable (G : Digraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance decidableBackDoor (X Y Z : Set V) [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)]
    [DecidablePred (· ∈ Z)] : Decidable (G.BackDoor X Y Z) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Decidable

end Digraph

namespace CausalInference.Criteria

/-- The directed graph on `Fin n` with the listed edges: a pair `(i, j)` is the edge `i → j`.
Used to state the examples of this directory. -/
def ofEdges {n : ℕ} (d : List (Fin n × Fin n)) : Digraph (Fin n) where
  Adj i j := (i, j) ∈ d

instance {n : ℕ} (d : List (Fin n × Fin n)) : DecidableRel (ofEdges d).Adj :=
  fun i j => inferInstanceAs (Decidable ((i, j) ∈ d))

end CausalInference.Criteria

namespace CausalInference.BackDoorExamples

open Criteria

/-- Pearl (2009), Figure 3.4, with `X₁, …, X₆` numbered `0, …, 5`, `Xᵢ = 6` and `Xⱼ = 7`; the
edges are `X₁ → X₃`, `X₁ → X₄`, `X₂ → X₄`, `X₂ → X₅`, `X₃ → Xᵢ`, `X₄ → Xᵢ`, `X₄ → Xⱼ`,
`X₅ → Xⱼ`, `Xᵢ → X₆`, `X₆ → Xⱼ`. -/
abbrev pearlFig34 : Digraph (Fin 8) :=
  ofEdges [(0, 2), (0, 3), (1, 3), (1, 4), (2, 6), (3, 6), (3, 7), (4, 7), (6, 5), (5, 7)]

example : pearlFig34.IsAcyclic := by decide +kernel
-- The text: `{X₃, X₄}` and `{X₄, X₅}` meet the criterion.
example : pearlFig34.BackDoor {6} {7} {2, 3} := by decide +kernel
example : pearlFig34.BackDoor {6} {7} {3, 4} := by decide +kernel
-- `{X₄}` does not: it leaves the path `Xᵢ ← X₃ ← X₁ → X₄ ← X₂ → X₅ → Xⱼ` open.
example : ¬ pearlFig34.BackDoor {6} {7} {3} := by decide +kernel
-- The caption: `{X₆}` is not admissible either; `X₆` is a descendant of `Xᵢ`.
example : ¬ pearlFig34.BackDoor {6} {7} {5} := by decide +kernel
-- The parents of `Xᵢ` are admissible, as `Digraph.IsAcyclic.backDoor_parents` asserts.
example : pearlFig34.parentsFinset 6 = {2, 3} := by decide +kernel

/-- What If, Figure 7.1: `L → A`, `L → Y`, `A → Y` with `L = 0`, `A = 1`, `Y = 2`. -/
abbrev whatIfFig71 : Digraph (Fin 3) := ofEdges [(0, 1), (0, 2), (1, 2)]

example : whatIfFig71.BackDoor {1} {2} {0} := by decide +kernel
example : ¬ whatIfFig71.BackDoor {1} {2} ∅ := by decide +kernel

/-- What If, Figure 7.4 (M-bias): `A ← U₂ → L ← U₁ → Y` and `A → Y`, with `A = 0`, `Y = 1`,
`L = 2`, `U₁ = 3`, `U₂ = 4`. -/
abbrev mBias : Digraph (Fin 5) := ofEdges [(4, 0), (4, 2), (3, 2), (3, 1), (0, 1)]

-- The empty set is admissible, while adjusting for the collider `L`, a non-descendant of `A`,
-- opens the back-door path through `L` and violates the criterion.
example : mBias.IsAcyclic := by decide +kernel
example : mBias.BackDoor {0} {1} ∅ := by decide +kernel
example : ¬ mBias.BackDoor {0} {1} {2} := by decide +kernel
example : mBias.BackDoor {0} {1} {2, 4} := by decide +kernel

/-- What If, Figure 7.5: Figure 7.4 with the extra edge `L → A`. -/
abbrev whatIfFig75 : Digraph (Fin 5) :=
  ofEdges [(4, 0), (4, 2), (3, 2), (3, 1), (0, 1), (2, 0)]

-- Intractable confounding: neither `∅` nor `{L}` is admissible.
example : ¬ whatIfFig75.BackDoor {0} {1} ∅ := by decide +kernel
example : ¬ whatIfFig75.BackDoor {0} {1} {2} := by decide +kernel

/-- What If, Figure 7.6: Figure 7.5 with `L₁` between `U₁` and `Y` and `L₂` between `U₂` and
`A`, so the edges `U₁ → Y` and `U₂ → A` become `U₁ → L₁ → Y` and `U₂ → L₂ → A`; here `L₁ = 5`
and `L₂ = 6`. -/
abbrev whatIfFig76 : Digraph (Fin 7) :=
  ofEdges [(4, 6), (6, 0), (4, 2), (3, 2), (3, 5), (5, 1), (0, 1), (2, 0)]

-- Measuring `L₁` alone, or `L₂` together with `L`, restores admissibility.
example : whatIfFig76.BackDoor {0} {1} {5} := by decide +kernel
example : whatIfFig76.BackDoor {0} {1} {6, 2} := by decide +kernel
example : ¬ whatIfFig76.BackDoor {0} {1} {2} := by decide +kernel

/-- The Primer, Figure 3.6: `Z → X`, `Z → W`, `W → Y`, `X → Y` with `X = 0`, `Y = 1`, `W = 2`
and the unmeasured `Z = 3`. -/
abbrev primerFig36 : Digraph (Fin 4) := ofEdges [(3, 0), (3, 2), (2, 1), (0, 1)]

example : primerFig36.BackDoor {0} {1} {2} := by decide +kernel
example : ¬ primerFig36.BackDoor {0} {1} ∅ := by decide +kernel

/-- The Primer, Figure 3.7: `E → X`, `E → Z`, `A → Z`, `A → Y`, `Z → X`, `Z → Y`, `X → Y` with
`X = 0`, `Y = 1`, `E = 2`, `A = 3`, `Z = 4`. -/
abbrev primerFig37 : Digraph (Fin 5) :=
  ofEdges [(2, 0), (2, 4), (3, 4), (3, 1), (4, 0), (4, 1), (0, 1)]

-- The admissible sets named in the text all contain the collider `Z`.
example : primerFig37.BackDoor {0} {1} {2, 4} := by decide +kernel
example : primerFig37.BackDoor {0} {1} {3, 4} := by decide +kernel
example : primerFig37.BackDoor {0} {1} {2, 3, 4} := by decide +kernel
example : ¬ primerFig37.BackDoor {0} {1} {4} := by decide +kernel
example : ¬ primerFig37.BackDoor {0} {1} {2, 3} := by decide +kernel
example : ¬ primerFig37.BackDoor {0} {1} ∅ := by decide +kernel

-- Adding the nondescendant `X₁` of `Xᵢ`, an ancestor of `X₃`, to `{X₃, X₄}` keeps the criterion
-- (`Digraph.BackDoor.insert_covariate_of_mem_ancestorsOf`).
example : pearlFig34.BackDoor {6} {7} {0, 2, 3} := by decide +kernel

/-- Several treatments, joint form against pairwise form: `x₂ → x₁`, `x₂ → y`, with `x₁ = 0`,
`x₂ = 1`, `y = 2`. The empty set passes the joint surgery test for `X = {x₁, x₂}`, while the
back-door path `x₁ ← x₂ → y` is open, so Pearl's pairwise test fails. The adjustment formula
`P(y | do(x₁, x₂)) = P(y | x₁, x₂)` holds here; the joint form is the one it needs. -/
theorem backDoor_not_pairwise_fork :
    (ofEdges (n := 3) [(1, 0), (1, 2)]).BackDoor {0, 1} {2} ∅ ∧
      ¬ (ofEdges (n := 3) [(1, 0), (1, 2)]).BackDoorPairwise {0, 1} {2} ∅ := by
  refine ⟨by decide +kernel, fun h => h.2 0 (by simp) 2 rfl ?_⟩
  exact ⟨1, [1, 2], by decide, Set.notMem_empty _,
    .fwd (by decide) (Set.notMem_empty _) (.nil (Set.notMem_empty _)), by decide⟩

/-- Several treatments with a common cause: `a → x₁`, `a → x₂`, `x₂ → y`, with `x₁ = 0`,
`x₂ = 1`, `y = 2`, `a = 3`. The empty set passes the joint surgery test for `X = {x₁, x₂}`, but
not the test for `x₁` alone, and Pearl's pairwise test fails through the open path
`x₁ ← a → x₂ → y`. -/
theorem backDoor_not_pairwise_common_cause :
    (ofEdges (n := 4) [(3, 0), (3, 1), (1, 2)]).BackDoor {0, 1} {2} ∅ ∧
      ¬ (ofEdges (n := 4) [(3, 0), (3, 1), (1, 2)]).BackDoor {0} {2} ∅ ∧
      ¬ (ofEdges (n := 4) [(3, 0), (3, 1), (1, 2)]).BackDoorPairwise {0, 1} {2} ∅ := by
  refine ⟨by decide +kernel, by decide +kernel, fun h => h.2 0 (by simp) 2 rfl ?_⟩
  exact ⟨3, [3, 1, 2], by decide, Set.notMem_empty _,
    .fwd (by decide) (Set.notMem_empty _)
      (.fwd (by decide) (Set.notMem_empty _) (.nil (Set.notMem_empty _))), by decide⟩

/-- The outcome as a covariate: for `y → x` (`x = 0`, `y = 1`), `{y}` passes `BackDoor` because
the endpoint `y` is conditioned on, but it is not an adjustment set. -/
example : (ofEdges (n := 2) [(1, 0)]).BackDoor {0} {1} {1} ∧
    ¬ (ofEdges (n := 2) [(1, 0)]).BackDoorAdjustment {0} {1} {1} :=
  ⟨by decide +kernel, fun h => Set.disjoint_left.1 h.2 rfl rfl⟩

end CausalInference.BackDoorExamples
