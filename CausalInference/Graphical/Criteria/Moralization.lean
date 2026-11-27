/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Criteria.BackDoor
public import CausalInference.Graphical.DSeparationExamples
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The moral graph and the ancestral moralization criterion

## Main definitions

* `Digraph.moralGraph G`: the moral graph of `G`, an undirected Mathlib `SimpleGraph` in which
  two distinct vertices are adjacent when they are joined by an edge of `G` in either direction
  or have a common child (they are co-parents, "married").
* `Digraph.avoidGraph H Z`: the steps of an undirected graph `H` between vertices outside `Z`,
  as a `Digraph`, so that the saturation procedure of the library decides reachability in it.
* `Digraph.USep H X Y Z`: `Z` separates `X` from `Y` in the undirected graph `H`: no path of
  `H` from a vertex of `X` to a vertex of `Y` avoids `Z` (endpoints included).
* `Digraph.MoralSep G X Y Z`: `Z` separates `X` from `Y` in the moral graph of the subgraph of
  `G` on the ancestral closure of `X ∪ Y ∪ Z` (Lauritzen et al. 1990).

## Main results

* `Digraph.dSep_iff_moralSep`: `G.DSep X Y Z ↔ G.MoralSep X Y Z`, the ancestral moral-graph
  criterion of Lauritzen, Dawid, Larsen and Leimer (1990), stated by Pearl (2009) on pp. 18 to 19.
  Both directions are proved, for every digraph (acyclicity is not used). The conventions match
  those of `Digraph.DSep`: an endpoint in `Z` is separated from everything, and a common vertex
  of `X` and `Y` outside `Z` is connected to itself.
* Decidability of `MoralSep`, and examples by `decide`.

## Proof outline

From an active trail to a moral path: every vertex of an active trail from `x` to `y` given `Z`
is an ancestor of `x`, `y` or `Z`; dropping the colliders, whose two neighbors on the trail are
co-parents, leaves a path of the moral graph through non-colliders, all outside `Z`.

From a moral path to an active trail: walk along the moral path keeping an active trail from
some vertex of `X` that can be continued in either direction. A moral edge through a common
child `c` that is an ancestor of `Z` is a collider that may be passed. Otherwise `c` is an
ancestor of `X` or of `Y` through a directed path avoiding `Z`: in the first case the trail is
restarted at that vertex of `X`, and in the second the trail is finished along that path.

## References

* S. L. Lauritzen, A. P. Dawid, B. N. Larsen, H.-G. Leimer (1990), *Independence properties of
  directed Markov fields*, Networks 20.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 1.2.3,
  pp. 18 to 19.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- The moral graph of `G`: two distinct vertices are adjacent when they are joined by an edge
of `G` in either direction or have a common child. -/
def moralGraph (G : Digraph V) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj v w

/-- The steps of the undirected graph `H` between two vertices outside `Z`, as a digraph. -/
def avoidGraph (H : SimpleGraph V) (Z : Set V) : Digraph V where
  Adj u v := H.Adj u v ∧ u ∉ Z ∧ v ∉ Z

/-- `USep H X Y Z`: `Z` separates `X` from `Y` in the undirected graph `H`: for every `x ∈ X`
outside `Z` and every `y ∈ Y`, no path of `H` from `x` to `y` has all its vertices outside
`Z`. -/
def USep (H : SimpleGraph V) (X Y Z : Set V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ∉ Z → ¬ ReflTransGen (avoidGraph H Z).Adj x y

/-- The ancestral moral-graph criterion (Lauritzen et al. 1990): `Z` separates `X` from `Y` in
the moral graph of the subgraph of `G` on the ancestral closure of `X ∪ Y ∪ Z`. -/
def MoralSep (G : Digraph V) (X Y Z : Set V) : Prop :=
  USep (G.restrict (G.ancestorsOf (X ∪ Y ∪ Z))).moralGraph X Y Z

variable {G : Digraph V} {X Y Z A : Set V} {u v w c p q x y : V} {a : Bool} {l : List V}

theorem moralGraph_adj :
    G.moralGraph.Adj u v ↔ u ≠ v ∧ ((G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj v w) ∨
      (G.Adj v u ∨ ∃ w, G.Adj v w ∧ G.Adj u w)) :=
  SimpleGraph.fromRel_adj _ _ _

theorem moralGraph_adj_of_adj (h : G.Adj u v) (hne : u ≠ v) : G.moralGraph.Adj u v :=
  moralGraph_adj.2 ⟨hne, Or.inl (Or.inl h)⟩

theorem moralGraph_adj_of_coparents (hu : G.Adj u w) (hv : G.Adj v w) (hne : u ≠ v) :
    G.moralGraph.Adj u v :=
  moralGraph_adj.2 ⟨hne, Or.inl (Or.inr ⟨w, hu, hv⟩)⟩

/-! ### From an active trail to a moral path -/

/-- The first vertex of a trail entered without an arrowhead is a non-collider, so it lies
outside `Z`. -/
theorem ActiveTrail.notMem_of_false (hp : G.ActiveTrail Z false u w l) : u ∉ Z := by
  cases hp with
  | nil hv => exact hv
  | fwd _ hu _ => exact hu
  | bwd _ hu _ => exact hu

/-- Every vertex of an active trail from `u` to `w` given `Z` is an ancestor of `w` or of `Z`,
or, if the trail was not entered at `u` through an arrowhead, of `u`. -/
theorem ActiveTrail.mem_ancestorsOf (hp : G.ActiveTrail Z a u w l) :
    ∀ t ∈ l, t ∈ G.ancestorsOf ({w} ∪ Z) ∨ (a = false ∧ t ∈ G.ancestorsOf {u}) := by
  induction hp with
  | nil hv =>
    intro t ht
    rw [List.mem_singleton] at ht
    exact Or.inl (subset_ancestorsOf _ (Or.inl ht))
  | @fwd a u v w l h hu q ih =>
    have ih' : ∀ t ∈ l, t ∈ G.ancestorsOf ({w} ∪ Z) := fun t ht =>
      (ih t ht).resolve_right fun h => Bool.noConfusion h.1
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact Or.inl (mem_ancestorsOf_of_adj h (ih' v q.head_mem))
    · exact Or.inl (ih' t ht)
  | @bwd u v w l h hu q ih =>
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact Or.inr ⟨rfl, subset_ancestorsOf _ rfl⟩
    · rcases ih t ht with h' | ⟨-, h'⟩
      · exact Or.inl h'
      · obtain ⟨s, hs, hts⟩ := h'
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact Or.inr ⟨rfl, u, rfl, hts.tail h⟩
  | @collider u v w l h hu q ih =>
    have hZ : G.ancestorsOf Z ⊆ G.ancestorsOf ({w} ∪ Z) :=
      ancestorsOf_mono Set.subset_union_right
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact Or.inl (hZ hu)
    · rcases ih t ht with h' | ⟨-, h'⟩
      · exact Or.inl h'
      · obtain ⟨s, hs, hts⟩ := h'
        rw [Set.mem_singleton_iff] at hs
        subst hs
        exact Or.inl (hZ (mem_ancestorsOf_of_reflTransGen (hts.tail h) hu))

/-- One step of a path in the moral graph of `G.restrict A` along an edge of `G` (in either
direction) between two vertices of `A` outside `Z`. -/
theorem reflTransGen_avoid_head_of_adj (h : G.Adj p u ∨ G.Adj u p) (hp : p ∈ A) (hu : u ∈ A)
    (hpZ : p ∉ Z) (huZ : u ∉ Z)
    (hr : ReflTransGen (avoidGraph (G.restrict A).moralGraph Z).Adj u w) :
    ReflTransGen (avoidGraph (G.restrict A).moralGraph Z).Adj p w := by
  rcases eq_or_ne p u with rfl | hne
  · exact hr
  · refine ReflTransGen.head ⟨?_, hpZ, huZ⟩ hr
    rcases h with h | h
    · exact moralGraph_adj_of_adj (G := G.restrict A) ⟨h, hp, hu⟩ hne
    · exact (moralGraph_adj_of_adj (G := G.restrict A) ⟨h, hu, hp⟩ hne.symm).symm

/-- One step of a path in the moral graph of `G.restrict A` between two co-parents in `A`
outside `Z` of a common child in `A`. -/
theorem reflTransGen_avoid_head_of_coparents (hpc : G.Adj p c) (hqc : G.Adj q c) (hp : p ∈ A)
    (hq : q ∈ A) (hc : c ∈ A) (hpZ : p ∉ Z) (hqZ : q ∉ Z)
    (hr : ReflTransGen (avoidGraph (G.restrict A).moralGraph Z).Adj q w) :
    ReflTransGen (avoidGraph (G.restrict A).moralGraph Z).Adj p w := by
  rcases eq_or_ne p q with rfl | hne
  · exact hr
  · exact ReflTransGen.head
      ⟨moralGraph_adj_of_coparents (G := G.restrict A) ⟨hpc, hp, hc⟩ ⟨hqc, hq, hc⟩ hne, hpZ, hqZ⟩
      hr

/-- An active trail given `Z` all of whose vertices lie in `A` yields a path of the moral graph
of `G.restrict A` avoiding `Z`, from its first vertex if that vertex is outside `Z`, and from
any parent of the first vertex in `A` outside `Z` if the trail was entered through an
arrowhead. -/
theorem ActiveTrail.reflTransGen_avoid (hp : G.ActiveTrail Z a u w l) (hl : ∀ t ∈ l, t ∈ A) :
    (u ∉ Z → ReflTransGen (avoidGraph (G.restrict A).moralGraph Z).Adj u w) ∧
      (a = true → ∀ q, G.Adj q u → q ∈ A → q ∉ Z →
        ReflTransGen (avoidGraph (G.restrict A).moralGraph Z).Adj q w) := by
  induction hp with
  | @nil a v hv =>
    have hvA := hl v List.mem_cons_self
    exact ⟨fun _ => ReflTransGen.refl, fun _ q hq hqA hqZ =>
      reflTransGen_avoid_head_of_adj (Or.inl hq) hqA hvA hqZ hv ReflTransGen.refl⟩
  | @fwd a u v w l h hu q ih =>
    have hl' : ∀ t ∈ l, t ∈ A := fun t ht => hl t (List.mem_cons_of_mem _ ht)
    have huA := hl u List.mem_cons_self
    have hmain := (ih hl').2 rfl u h huA hu
    exact ⟨fun _ => hmain, fun _ r hr hrA hrZ =>
      reflTransGen_avoid_head_of_adj (Or.inl hr) hrA huA hrZ hu hmain⟩
  | @bwd u v w l h hu q ih =>
    have hl' : ∀ t ∈ l, t ∈ A := fun t ht => hl t (List.mem_cons_of_mem _ ht)
    have huA := hl u List.mem_cons_self
    have hvA := hl' v q.head_mem
    have hvZ := q.notMem_of_false
    exact ⟨fun _ => reflTransGen_avoid_head_of_adj (Or.inr h) huA hvA hu hvZ
      ((ih hl').1 hvZ), fun h => Bool.noConfusion h⟩
  | @collider u v w l h hu q ih =>
    have hl' : ∀ t ∈ l, t ∈ A := fun t ht => hl t (List.mem_cons_of_mem _ ht)
    have huA := hl u List.mem_cons_self
    have hvA := hl' v q.head_mem
    have hvZ := q.notMem_of_false
    have hv := (ih hl').1 hvZ
    exact ⟨fun huZ => reflTransGen_avoid_head_of_adj (Or.inr h) huA hvA huZ hvZ hv,
      fun _ r hr hrA hrZ => reflTransGen_avoid_head_of_coparents hr h hrA hvA huA hrZ hvZ hv⟩

/-- d-connection implies connection in the ancestral moral graph. -/
theorem DConn.not_moralSep (h : G.DConn X Y Z) : ¬ G.MoralSep X Y Z := by
  obtain ⟨x, hx, y, hy, l, hl⟩ := dConn_iff_dConnTrail.1 h
  have hA : ∀ t ∈ l, t ∈ G.ancestorsOf (X ∪ Y ∪ Z) := by
    intro t ht
    rcases hl.mem_ancestorsOf t ht with h' | ⟨-, h'⟩
    · refine ancestorsOf_mono ?_ h'
      rintro s (hs | hs)
      · rw [Set.mem_singleton_iff] at hs
        exact Or.inl (Or.inr (hs ▸ hy))
      · exact Or.inr hs
    · refine ancestorsOf_mono ?_ h'
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      exact Or.inl (Or.inl (hs ▸ hx))
  have hxZ := hl.notMem_of_false
  exact fun hsep => hsep x hx y hy hxZ ((hl.reflTransGen_avoid hA).1 hxZ)

/-! ### From a moral path to an active trail -/

/-- A directed path into `x` from a vertex that is not an ancestor of `Z`, read backward, is an
active trail given `Z`. -/
theorem reflTransGen_bayesBall_of_reflTransGen_backward (h : ReflTransGen G.Adj u x)
    (hu : u ∉ G.ancestorsOf Z) : ReflTransGen (G.bayesBall Z).Adj (x, false) (u, false) := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ReflTransGen.refl
  | @head a b hab _ ih =>
    have hb : b ∉ G.ancestorsOf Z := fun hb => hu (mem_ancestorsOf_of_adj hab hb)
    exact (ih hb).tail (bayesBall_adj_false_false.2 ⟨hab, fun h => hb (subset_ancestorsOf Z h)⟩)

/-- A vertex `c` of the ancestral closure of `X ∪ Y ∪ Z` reached through an arrowhead by an
active trail from `X` is an ancestor of `Z`, or it is not and a vertex of `X` outside `Z`
reaches `(c, false)` by an active trail, or `X` and `Y` are d-connected. -/
theorem arrive_or (hx : x ∈ X) (hxZ : x ∉ Z)
    (hreach : ReflTransGen (G.bayesBall Z).Adj (x, false) (c, true))
    (hc : c ∈ G.ancestorsOf (X ∪ Y ∪ Z)) :
    G.DConn X Y Z ∨ c ∈ G.ancestorsOf Z ∨ (c ∉ G.ancestorsOf Z ∧
      ∃ t ∈ X, t ∉ Z ∧ ReflTransGen (G.bayesBall Z).Adj (t, false) (c, false)) := by
  by_cases hcZ : c ∈ G.ancestorsOf Z
  · exact Or.inr (Or.inl hcZ)
  obtain ⟨s, hs, hcs⟩ := hc
  have hsZ : s ∉ Z := fun h => hcZ ⟨s, h, hcs⟩
  rcases hs with (hs | hs) | hs
  · exact Or.inr (Or.inr ⟨hcZ, s, hs, hsZ,
      reflTransGen_bayesBall_of_reflTransGen_backward hcs hcZ⟩)
  · obtain ⟨e, he⟩ := exists_reflTransGen_bayesBall_of_reflTransGen hcs hcZ true
    exact Or.inl ⟨x, hx, s, hs, hxZ, hsZ, e, hreach.trans he⟩
  · exact absurd hs hsZ

/-- The invariant of the walk along a moral path: some vertex `x ∈ X` outside `Z` reaches
`(u, b)` by an active trail that can be continued from `u` in either direction. -/
def MoralGood (G : Digraph V) (X Z : Set V) (u : V) : Prop :=
  ∃ x ∈ X, x ∉ Z ∧ ∃ b, ReflTransGen (G.bayesBall Z).Adj (x, false) (u, b) ∧
    (b = false ∨ u ∈ G.ancestorsOf Z)

/-- Arriving at `c` through an arrowhead with `c` in the ancestral closure: the trail can be
continued backward from `c` along any edge `v → c`, unless `X` and `Y` are already
d-connected. -/
theorem moralGood_of_arrive (hx : x ∈ X) (hxZ : x ∉ Z)
    (hreach : ReflTransGen (G.bayesBall Z).Adj (x, false) (c, true))
    (hc : c ∈ G.ancestorsOf (X ∪ Y ∪ Z)) (hvc : G.Adj v c) :
    G.DConn X Y Z ∨ G.MoralGood X Z v := by
  rcases arrive_or hx hxZ hreach hc with h | hcZ | ⟨hcZ, t, ht, htZ, htc⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, hx, hxZ, false, hreach.tail (bayesBall_adj_true_false.2 ⟨hvc, hcZ⟩),
      Or.inl rfl⟩
  · exact Or.inr ⟨t, ht, htZ, false, htc.tail (bayesBall_adj_false_false.2
      ⟨hvc, fun h => hcZ (subset_ancestorsOf Z h)⟩), Or.inl rfl⟩

/-- Arriving at `c` through an arrowhead with `c` in the ancestral closure: `c` itself is good,
unless `X` and `Y` are already d-connected. -/
theorem moralGood_self_of_arrive (hx : x ∈ X) (hxZ : x ∉ Z)
    (hreach : ReflTransGen (G.bayesBall Z).Adj (x, false) (c, true))
    (hc : c ∈ G.ancestorsOf (X ∪ Y ∪ Z)) : G.DConn X Y Z ∨ G.MoralGood X Z c := by
  rcases arrive_or hx hxZ hreach hc with h | hcZ | ⟨-, t, ht, htZ, htc⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, hx, hxZ, true, hreach, Or.inr hcZ⟩
  · exact Or.inr ⟨t, ht, htZ, false, htc, Or.inl rfl⟩

/-- One step of the walk: from a good vertex `u` outside `Z`, a step of the moral graph of the
ancestral subgraph to a vertex `v` leads to a good vertex, unless `X` and `Y` are
already d-connected. -/
theorem MoralGood.step (hu : G.MoralGood X Z u) (huZ : u ∉ Z)
    (huv : (G.restrict (G.ancestorsOf (X ∪ Y ∪ Z))).moralGraph.Adj u v) :
    G.DConn X Y Z ∨ G.MoralGood X Z v := by
  obtain ⟨x, hx, hxZ, b, hreach, hb⟩ := hu
  have hfwd : ∀ {d}, G.Adj u d → ReflTransGen (G.bayesBall Z).Adj (x, false) (d, true) :=
    fun hud => hreach.tail (bayesBall_adj_true.2 ⟨hud, huZ⟩)
  have hbwd : G.Adj v u → G.MoralGood X Z v := fun hvu => by
    refine ⟨x, hx, hxZ, false, hreach.tail ?_, Or.inl rfl⟩
    cases b
    · exact bayesBall_adj_false_false.2 ⟨hvu, huZ⟩
    · exact bayesBall_adj_true_false.2 ⟨hvu, hb.resolve_left (fun h => Bool.noConfusion h)⟩
  obtain ⟨-, h⟩ := moralGraph_adj.1 huv
  rcases h with (h | ⟨c, huc, hvc⟩) | (h | ⟨c, hvc, huc⟩)
  · exact moralGood_self_of_arrive hx hxZ (hfwd h.1) h.2.2
  · exact moralGood_of_arrive hx hxZ (hfwd huc.1) huc.2.2 hvc.1
  · exact Or.inr (hbwd h.1)
  · exact moralGood_of_arrive hx hxZ (hfwd huc.1) huc.2.2 hvc.1

/-- Connection in the ancestral moral graph implies d-connection. -/
theorem dConn_of_not_moralSep (h : ¬ G.MoralSep X Y Z) : G.DConn X Y Z := by
  simp only [MoralSep, USep, not_forall, not_not, exists_prop] at h
  obtain ⟨x, hx, y, hy, hxZ, hpath⟩ := h
  have key : ∀ w, ReflTransGen
      (avoidGraph (G.restrict (G.ancestorsOf (X ∪ Y ∪ Z))).moralGraph Z).Adj x w →
      w ∉ Z → G.DConn X Y Z ∨ G.MoralGood X Z w := by
    intro w hw hwZ
    induction hw with
    | refl => exact Or.inr ⟨x, hx, hxZ, false, ReflTransGen.refl, Or.inl rfl⟩
    | @tail b d _ hbd ih =>
      rcases ih hbd.2.1 with h | h
      · exact Or.inl h
      · exact h.step hbd.2.1 hbd.1
  have hyZ : y ∉ Z := by
    rcases hpath.cases_tail with h | ⟨b, -, hb⟩
    · rw [h]
      exact hxZ
    · exact hb.2.2
  rcases key y hpath hyZ with h | ⟨x', hx', hx'Z, b, hreach, -⟩
  · exact h
  · exact ⟨x', hx', y, hy, hx'Z, hyZ, b, hreach⟩

/-! ### The criterion -/

/-- The ancestral moral-graph criterion (Lauritzen, Dawid, Larsen, Leimer 1990; Pearl 2009,
pp. 18 to 19): `X` and `Y` are d-separated by `Z` in `G` if and only if `Z` separates `X` from
`Y` in the moral graph of the subgraph of `G` on the ancestral closure of `X ∪ Y ∪ Z`. -/
theorem dSep_iff_moralSep : G.DSep X Y Z ↔ G.MoralSep X Y Z :=
  ⟨fun h => by_contra fun h' => h (dConn_of_not_moralSep h'),
    fun h h' => h'.not_moralSep h⟩

section Decidable

variable (G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance decidableRelMoralGraph : DecidableRel G.moralGraph.Adj := fun _ _ =>
  decidable_of_iff _ moralGraph_adj.symm

instance decidableRelAvoidGraph (H : SimpleGraph V) [DecidableRel H.Adj] (Z : Set V)
    [DecidablePred (· ∈ Z)] : DecidableRel (avoidGraph H Z).Adj :=
  fun u v => inferInstanceAs (Decidable (H.Adj u v ∧ u ∉ Z ∧ v ∉ Z))

instance decidableUSep (H : SimpleGraph V) [DecidableRel H.Adj] (X Y Z : Set V)
    [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)] [DecidablePred (· ∈ Z)] :
    Decidable (USep H X Y Z) := by
  unfold USep
  infer_instance

instance decidableMoralSep (X Y Z : Set V) [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)]
    [DecidablePred (· ∈ Z)] : Decidable (G.MoralSep X Y Z) := by
  haveI : DecidablePred (· ∈ X ∪ Y ∪ Z) := fun v =>
    inferInstanceAs (Decidable ((v ∈ X ∨ v ∈ Y) ∨ v ∈ Z))
  unfold MoralSep
  infer_instance

end Decidable

end Digraph

namespace CausalInference.MoralizationExamples

open GraphExamples DSeparationExamples

-- The collider `0 → 2 ← 1`: marginally the ancestral set is `{0, 1}`, with no moral edge; given
-- the collider, the parents are married.
example : collider.MoralSep {0} {1} ∅ := by decide +kernel
example : ¬ collider.MoralSep {0} {1} {2} := by decide +kernel
example : collider.moralGraph.Adj 0 1 := by decide +kernel

-- The M-structure and the six-vertex graph: the moral test gives the same answers as the
-- d-separation statements of `CausalInference.Graphical.DSeparationExamples`.
example : mStructure.MoralSep {0} {4} ∅ := by decide +kernel
example : ¬ mStructure.MoralSep {0} {4} {2} := by decide +kernel
example : mStructure.MoralSep {0} {4} {1, 2} := by decide +kernel
example : six.MoralSep {0} {2} ∅ := by decide +kernel
example : ¬ six.MoralSep {0} {2} {3} := by decide +kernel
example : six.MoralSep {0} {4} {3, 5} := by decide +kernel

-- Moralizing the whole graph instead of the ancestral subgraph loses separations: in the
-- collider, the parents are married in the full moral graph even with nothing conditioned on.
example : ¬ Digraph.USep collider.moralGraph {0} {1} ∅ := by decide +kernel

end CausalInference.MoralizationExamples
