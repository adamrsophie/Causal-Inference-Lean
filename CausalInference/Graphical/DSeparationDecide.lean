/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.DSeparation

/-!
# Deciding d-separation, and the textbook path definition

The definition `Digraph.DConn` of `CausalInference.Graphical.DSeparation` is reachability in the
Bayes-ball state graph. This file states the textbook definitions by active trails and by active
simple paths, proves that both agree with `Digraph.DConn`, and derives decidability of
d-separation on finite graphs.

## Main definitions

* `Digraph.ActiveTrail G Z a u w l`: `l` is the vertex sequence of a trail from `u` to `w` that
  is active given `Z`; `a = true` records that the trail was entered at `u` through an
  arrowhead at `u`. A whole trail between two vertices has `a = false`.
* `Digraph.DConnTrail G X Y Z`: some active trail joins a vertex of `X` to a vertex of `Y`.
* `Digraph.DConnPath G X Y Z`: some active simple path (no repeated vertex) joins a vertex of
  `X` to a vertex of `Y`. This is the textbook definition of d-connection.

## Main results

* `Digraph.dConn_iff_dConnTrail`: the Bayes-ball definition agrees with active trails.
* `Digraph.dConn_iff_dConnPath`: the Bayes-ball definition agrees with active simple paths.
  The proof shortens any active trail with a repeated vertex: if a vertex occurs twice, cutting
  out the loop between the occurrences keeps the trail active. This is the main correctness
  theorem of the decision procedure.
* `Digraph.dSep_iff_forall_path`: d-separation is the blocking of every simple path.
* `Decidable (G.DSep X Y Z)` for a finite vertex type with decidable adjacency and decidable
  membership in `X`, `Y`, `Z`; it computes reachability in the finite state graph `V × Bool`
  with `Digraph.reachFinset`, so `decide` works on concrete graphs.

See Pearl (2009), *Causality*, section 1.2.3, and Shachter (1998), *Bayes-Ball*.
-/

@[expose] public section

namespace Digraph

open Relation

variable {V : Type*}

/-- `G.ActiveTrail Z a u w l`: `l` is the list of vertices of a trail from `u` to `w` in `G`
that is active given `Z`. A trail is a walk in the underlying undirected graph whose steps each
use an edge of `G` in either direction. The flag `a = true` records that the trail was entered
at `u` through an arrowhead at `u`. The constructors are:

* `nil`: the one-vertex trail at `v`; its vertex is an endpoint, hence a non-collider, so
  `v ∉ Z`;
* `fwd`: a step along `u → v`; the trail leaves `u` through a tail, so `u` is a non-collider
  and `u ∉ Z`;
* `bwd`: a step along `u ← v` from a vertex `u` not entered through an arrowhead; `u` is a
  non-collider and `u ∉ Z`;
* `collider`: a step along `u ← v` from a vertex `u` entered through an arrowhead; `u` is a
  collider and must lie in `G.ancestorsOf Z` (it or a descendant is in `Z`). -/
inductive ActiveTrail (G : Digraph V) (Z : Set V) : Bool → V → V → List V → Prop
  | nil {a : Bool} {v : V} (hv : v ∉ Z) : ActiveTrail G Z a v v [v]
  | fwd {a : Bool} {u v w : V} {l : List V} (h : G.Adj u v) (hu : u ∉ Z)
      (p : ActiveTrail G Z true v w l) : ActiveTrail G Z a u w (u :: l)
  | bwd {u v w : V} {l : List V} (h : G.Adj v u) (hu : u ∉ Z)
      (p : ActiveTrail G Z false v w l) : ActiveTrail G Z false u w (u :: l)
  | collider {u v w : V} {l : List V} (h : G.Adj v u) (hu : u ∈ G.ancestorsOf Z)
      (p : ActiveTrail G Z false v w l) : ActiveTrail G Z true u w (u :: l)

/-- `G.DConnTrail X Y Z`: a vertex of `X` and a vertex of `Y` are joined by a trail that is
active given `Z` (vertices may repeat). -/
def DConnTrail (G : Digraph V) (X Y Z : Set V) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, ∃ l, G.ActiveTrail Z false x y l

/-- `G.DConnPath X Y Z`: a vertex of `X` and a vertex of `Y` are joined by a simple path (no
repeated vertex) that is active given `Z`: every collider of the path is in `G.ancestorsOf Z`
and every other vertex of the path, endpoints included, is outside `Z`. This is the textbook
definition of d-connection. -/
def DConnPath (G : Digraph V) (X Y Z : Set V) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, ∃ l, G.ActiveTrail Z false x y l ∧ l.Nodup

variable {G : Digraph V} {X Y Z : Set V} {u v w : V} {a b : Bool} {l : List V}

/-! ### Trails and the state graph -/

/-- An active trail is a path of the Bayes-ball state graph ending outside `Z`. -/
theorem ActiveTrail.reflTransGen (p : G.ActiveTrail Z a u w l) :
    w ∉ Z ∧ ∃ e, ReflTransGen (G.bayesBall Z).Adj (u, a) (w, e) := by
  induction p with
  | @nil a v hv => exact ⟨hv, a, ReflTransGen.refl⟩
  | fwd h hu _ ih =>
    obtain ⟨hw, e, he⟩ := ih
    exact ⟨hw, e, ReflTransGen.head (bayesBall_adj_true.2 ⟨h, hu⟩) he⟩
  | bwd h hu _ ih =>
    obtain ⟨hw, e, he⟩ := ih
    exact ⟨hw, e, ReflTransGen.head (bayesBall_adj_false_false.2 ⟨h, hu⟩) he⟩
  | collider h hu _ ih =>
    obtain ⟨hw, e, he⟩ := ih
    exact ⟨hw, e, ReflTransGen.head (bayesBall_adj_true_false.2 ⟨h, hu⟩) he⟩

/-- Prepending one step of the state graph to an active trail. -/
theorem ActiveTrail.cons {d : Bool} (h : (G.bayesBall Z).Adj (u, a) (v, d))
    (p : G.ActiveTrail Z d v w l) : G.ActiveTrail Z a u w (u :: l) := by
  cases d
  · cases a
    · obtain ⟨hvu, hu⟩ := bayesBall_adj_false_false.1 h
      exact .bwd hvu hu p
    · obtain ⟨hvu, hu⟩ := bayesBall_adj_true_false.1 h
      exact .collider hvu hu p
  · obtain ⟨huv, hu⟩ := bayesBall_adj_true.1 h
    exact .fwd huv hu p

/-- A path of the Bayes-ball state graph ending outside `Z` gives an active trail. -/
theorem exists_activeTrail_of_reflTransGen {s : V × Bool} {e : Bool}
    (h : ReflTransGen (G.bayesBall Z).Adj s (w, e)) (hw : w ∉ Z) :
    ∃ l, G.ActiveTrail Z s.2 s.1 w l := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨[w], .nil hw⟩
  | @head s t hst _ ih =>
    obtain ⟨l, hl⟩ := ih
    exact ⟨s.1 :: l, ActiveTrail.cons hst hl⟩

/-- The Bayes-ball definition of d-connection agrees with the definition by active trails. -/
theorem dConn_iff_dConnTrail : G.DConn X Y Z ↔ G.DConnTrail X Y Z := by
  constructor
  · rintro ⟨x, hx, y, hy, -, hyZ, b, hxy⟩
    obtain ⟨l, hl⟩ := exists_activeTrail_of_reflTransGen hxy hyZ
    exact ⟨x, hx, y, hy, l, hl⟩
  · rintro ⟨x, hx, y, hy, l, hl⟩
    obtain ⟨hyZ, e, he⟩ := hl.reflTransGen
    have hxZ : x ∉ Z := by
      cases hl with
      | nil hv => exact hv
      | fwd _ hu _ => exact hu
      | bwd _ hu _ => exact hu
    exact ⟨x, hx, y, hy, hxZ, hyZ, e, he⟩

/-! ### Shortening trails to simple paths -/

/-- The suffix of an active trail from a later occurrence of a vertex `x` is an active trail
from `x`, for the arrival flag `b` of that occurrence, and the state graph reaches `(x, b)`
from the start. -/
theorem ActiveTrail.exists_suffix {x : V} (p : G.ActiveTrail Z a u w l) (hx : x ∈ l) :
    ∃ b l', l' <:+ l ∧ G.ActiveTrail Z b x w l' ∧
      ReflTransGen (G.bayesBall Z).Adj (u, a) (x, b) := by
  induction p with
  | @nil a v hv =>
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨a, [x], List.suffix_refl _, .nil hv, ReflTransGen.refl⟩
  | @fwd a u v w l h hu q ih =>
    by_cases hxu : x = u
    · subst hxu
      exact ⟨a, _, List.suffix_refl _, .fwd h hu q, ReflTransGen.refl⟩
    · obtain ⟨b, l', hsuf, hl', hr⟩ := ih ((List.mem_cons.1 hx).resolve_left hxu)
      exact ⟨b, l', hsuf.trans (List.suffix_cons _ _), hl',
        ReflTransGen.head (bayesBall_adj_true.2 ⟨h, hu⟩) hr⟩
  | @bwd u v w l h hu q ih =>
    by_cases hxu : x = u
    · subst hxu
      exact ⟨false, _, List.suffix_refl _, .bwd h hu q, ReflTransGen.refl⟩
    · obtain ⟨b, l', hsuf, hl', hr⟩ := ih ((List.mem_cons.1 hx).resolve_left hxu)
      exact ⟨b, l', hsuf.trans (List.suffix_cons _ _), hl',
        ReflTransGen.head (bayesBall_adj_false_false.2 ⟨h, hu⟩) hr⟩
  | @collider u v w l h hu q ih =>
    by_cases hxu : x = u
    · subst hxu
      exact ⟨true, _, List.suffix_refl _, .collider h hu q, ReflTransGen.refl⟩
    · obtain ⟨b, l', hsuf, hl', hr⟩ := ih ((List.mem_cons.1 hx).resolve_left hxu)
      exact ⟨b, l', hsuf.trans (List.suffix_cons _ _), hl',
        ReflTransGen.head (bayesBall_adj_true_false.2 ⟨h, hu⟩) hr⟩

/-- Cutting out a loop: if the state graph leads from `(u, a)` back to `(u, b)`, then an active
trail from `u` entered with flag `b` is also active when entered with flag `a`. -/
theorem ActiveTrail.of_reflTransGen_loop (p : G.ActiveTrail Z b u w l)
    (h : ReflTransGen (G.bayesBall Z).Adj (u, a) (u, b)) : G.ActiveTrail Z a u w l := by
  cases p with
  | nil hv => exact .nil hv
  | fwd hadj hu q => exact .fwd hadj hu q
  | bwd hadj hu q =>
    cases a
    · exact .bwd hadj hu q
    · exact .collider hadj (mem_ancestorsOf_of_reflTransGen_bayesBall h rfl) q
  | collider hadj hu q =>
    cases a
    · rcases h.cases_head with heq | ⟨t, ht, -⟩
      · simp at heq
      · exact .bwd hadj (notMem_of_bayesBall_adj_false ht) q
    · exact .collider hadj hu q

/-- A path of the Bayes-ball state graph ending outside `Z` gives an active simple path. -/
theorem exists_activeTrail_nodup_of_reflTransGen {s : V × Bool} {e : Bool}
    (h : ReflTransGen (G.bayesBall Z).Adj s (w, e)) (hw : w ∉ Z) :
    ∃ l, G.ActiveTrail Z s.2 s.1 w l ∧ l.Nodup := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨[w], .nil hw, List.nodup_singleton w⟩
  | @head s t hst _ ih =>
    obtain ⟨l, hl, hnd⟩ := ih
    by_cases hs : s.1 ∈ l
    · obtain ⟨b, l', hsuf, hl', hr⟩ := hl.exists_suffix hs
      exact ⟨l', hl'.of_reflTransGen_loop (ReflTransGen.head hst hr),
        hnd.sublist hsuf.sublist⟩
    · exact ⟨s.1 :: l, ActiveTrail.cons hst hl, List.nodup_cons.2 ⟨hs, hnd⟩⟩

/-- The Bayes-ball definition of d-connection agrees with the textbook definition by active
simple paths. -/
theorem dConn_iff_dConnPath : G.DConn X Y Z ↔ G.DConnPath X Y Z := by
  constructor
  · rintro ⟨x, hx, y, hy, -, hyZ, b, hxy⟩
    obtain ⟨l, hl, hnd⟩ := exists_activeTrail_nodup_of_reflTransGen hxy hyZ
    exact ⟨x, hx, y, hy, l, hl, hnd⟩
  · rintro ⟨x, hx, y, hy, l, hl, -⟩
    exact dConn_iff_dConnTrail.2 ⟨x, hx, y, hy, l, hl⟩

/-- Active trails and active simple paths give the same notion of d-connection. -/
theorem dConnTrail_iff_dConnPath : G.DConnTrail X Y Z ↔ G.DConnPath X Y Z :=
  dConn_iff_dConnTrail.symm.trans dConn_iff_dConnPath

/-- `X` and `Y` are d-separated by `Z` exactly when no simple path between a vertex of `X` and
a vertex of `Y` is active given `Z`. -/
theorem dSep_iff_forall_path :
    G.DSep X Y Z ↔ ∀ x ∈ X, ∀ y ∈ Y, ∀ l, l.Nodup → ¬ G.ActiveTrail Z false x y l := by
  rw [DSep, dConn_iff_dConnPath, DConnPath]
  simp only [not_exists, not_and]
  exact forall₂_congr fun _ _ => forall₂_congr fun _ _ => forall_congr' fun _ => imp_not_comm

/-! ### Decidability -/

section Decidable

variable (G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance decidableMemAncestorsOf (S : Set V) [DecidablePred (· ∈ S)] :
    DecidablePred (· ∈ G.ancestorsOf S) :=
  fun u => decidable_of_iff (∃ s, s ∈ S ∧ ReflTransGen G.Adj u s) (by simp)

instance decidablePasses (Z : Set V) [DecidablePred (· ∈ Z)] (v : V) (b c : Bool) :
    Decidable (G.Passes Z v b c) :=
  inferInstanceAs (Decidable (if b = true ∧ c = false then _ else _))

instance decidableRelBayesBall (Z : Set V) [DecidablePred (· ∈ Z)] :
    DecidableRel (G.bayesBall Z).Adj :=
  fun s t => inferInstanceAs
    (Decidable ((if t.2 then G.Adj s.1 t.1 else G.Adj t.1 s.1) ∧ G.Passes Z s.1 s.2 t.2))

instance decidableDConn (X Y Z : Set V) [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)]
    [DecidablePred (· ∈ Z)] : Decidable (G.DConn X Y Z) :=
  inferInstanceAs (Decidable (∃ x ∈ X, _))

instance decidableDSep (X Y Z : Set V) [DecidablePred (· ∈ X)] [DecidablePred (· ∈ Y)]
    [DecidablePred (· ∈ Z)] : Decidable (G.DSep X Y Z) :=
  inferInstanceAs (Decidable (¬ _))

end Decidable

end Digraph
