/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Districts

/-!
# Latent projection

Given a directed mixed graph `G` on `V` and a set `L` of latent vertices, the latent projection
of `G` onto the observed vertices `V \ L` keeps the vertex type `V` and makes every latent vertex
isolated. Its edges between observed vertices `u` and `v` are:

* a directed edge `u → v` when `G` has a directed path from `u` to `v` with at least one edge,
  all of whose interior vertices are latent;
* a bidirected edge `u ↔ v`, for `u ≠ v`, when `G` has a path between `u` and `v` with latent
  interior vertices, no collider, and arrowheads at both ends. Such a path has one of two shapes:
  a latent source `l` with directed latent-interior paths from `l` to `u` and from `l` to `v`;
  or a single bidirected edge `a ↔ b` of `G` with `a = u` or a directed latent-interior path from
  a latent `a` to `u`, and likewise for `b` and `v`. The definition `ADMG.project` lists these
  two shapes explicitly, and `ADMG.projectBiAdj_iff_exists_path` proves that they are exactly
  the path criterion, with colliders read off the edge marks.

For a DAG (`ADMG.ofDigraph D`) only the first shape occurs, and `latentProjection D L` has a
bidirected edge `u ↔ v` exactly when some latent `l` has directed latent-interior paths to both
(`latentProjection_bidirected_adj`).

Keeping the vertex type `V` instead of passing to the subtype of observed vertices makes the
two-stage theorem `ADMG.project_project` an equation between graphs on the same type, and lets
every statement about ancestors use the ancestor relation of the substrate unchanged.

## Main definitions

* `CausalInference.LatentPath D L a b`: a directed path of positive length from `a` to `b` in
  `D` whose interior vertices lie in `L`.
* `CausalInference.LatentAnc D L a b`: `a = b`, or `a ∈ L` and `LatentPath D L a b`.
* `ADMG.project G L`: the latent projection of a directed mixed graph.
* `CausalInference.latentProjection D L`: the latent projection of a directed graph, as an
  ADMG.
* `ADMG.LatentTrail`, `ADMG.ProjectionTrail`, `ADMG.DirectedProjectionTrail`: walks (with their
  vertex lists) with latent interior and no collider, used to state the path criterion.

## Main results

* `ADMG.IsAcyclic.project`, `latentProjection_isAcyclic`: the projection of an acyclic graph is
  acyclic.
* `ADMG.isAncestor_project_iff`, `isAncestor_latentProjection_iff`: for observed `u` and `v`,
  `u` is an ancestor of `v` in the projection exactly when it is in the original graph.
* `ADMG.project_empty`, `latentProjection_empty`: projecting out nothing gives the graph back;
  for a DAG, the DAG with no bidirected edges.
* `ADMG.project_project`, `latentProjection_project`: projecting out `L1` and then `L2` is
  projecting out `L1 ∪ L2` in one step.
* `ADMG.projectBiAdj_iff_exists_path` (and `ADMG.projectBiAdj_iff_exists_trail` for walks):
  `u ↔ v` in the projection exactly when `u` and `v` are observed and joined by a path with no
  repeated vertex, latent interior, no collider, and arrowheads at both ends.
* `ADMG.project_directed_adj_iff_exists_path`: for `u ≠ v`, `u → v` in the projection exactly
  when `u` and `v` are observed and joined by a directed path with latent interior.
* `ADMG.project_deleteIncoming`, `ADMG.project_deleteOutgoing`,
  `latentProjection_deleteIncoming`, `latentProjection_deleteOutgoing`: for `X` disjoint from
  `L`, projection commutes with both mutilations.
* `ADMG.district_project_of_mem`: a latent vertex is alone in its district of the projection.

Sources: Verma and Pearl (1990), *Equivalence and synthesis of causal models*; Pearl (2009),
*Causality: Models, Reasoning, and Inference*, 2nd edition; Richardson (2003), *Markov properties
for acyclic directed mixed graphs*.
-/

@[expose] public section

namespace CausalInference

open Relation

variable {V : Type*}

/-! ### Directed paths with latent interior -/

/-- The edges of `D` that end in `L`: the steps a latent-interior path may take before its last
edge. -/
def latentStepDigraph (D : Digraph V) (L : Set V) : Digraph V where
  Adj a b := D.Adj a b ∧ b ∈ L

/-- `LatentPath D L a b`: there is a directed path in `D` from `a` to `b` with at least one edge,
all of whose interior vertices lie in `L` (the endpoints are unrestricted). -/
def LatentPath (D : Digraph V) (L : Set V) (a b : V) : Prop :=
  ∃ w, ReflTransGen (latentStepDigraph D L).Adj a w ∧ D.Adj w b

/-- `LatentAnc D L a b`: either `a = b`, or `a` is latent and `LatentPath D L a b`. This is the
end segment `a → ⋯ → b` of a collider-free latent-interior path that arrives at `b` with an
arrowhead, starting from a latent vertex or from the bidirected edge at `a = b`. -/
def LatentAnc (D : Digraph V) (L : Set V) (a b : V) : Prop :=
  a = b ∨ (a ∈ L ∧ LatentPath D L a b)

section LatentPath

variable {D : Digraph V} {L L' : Set V} {a b c : V}

@[simp] theorem latentStepDigraph_adj : (latentStepDigraph D L).Adj a b ↔ D.Adj a b ∧ b ∈ L :=
  Iff.rfl

/-- An edge is a latent-interior path. -/
theorem latentPath_of_adj (h : D.Adj a b) : LatentPath D L a b := ⟨a, ReflTransGen.refl, h⟩

/-- Prepending latent steps to a latent-interior path. -/
theorem LatentPath.of_reflTransGen (hab : ReflTransGen (latentStepDigraph D L).Adj a b)
    (hbc : LatentPath D L b c) : LatentPath D L a c :=
  let ⟨w, hbw, hwc⟩ := hbc
  ⟨w, hab.trans hbw, hwc⟩

/-- Prepending an edge into a latent vertex. -/
theorem LatentPath.head (hab : D.Adj a b) (hb : b ∈ L) (hbc : LatentPath D L b c) :
    LatentPath D L a c :=
  LatentPath.of_reflTransGen (ReflTransGen.single ⟨hab, hb⟩) hbc

/-- A latent-interior path that ends in a latent vertex is a sequence of latent steps. -/
theorem LatentPath.reflTransGen (hab : LatentPath D L a b) (hb : b ∈ L) :
    ReflTransGen (latentStepDigraph D L).Adj a b :=
  let ⟨_, haw, hwb⟩ := hab
  haw.tail ⟨hwb, hb⟩

/-- Concatenation of latent-interior paths through a latent vertex. -/
theorem LatentPath.trans (hab : LatentPath D L a b) (hb : b ∈ L) (hbc : LatentPath D L b c) :
    LatentPath D L a c :=
  LatentPath.of_reflTransGen (hab.reflTransGen hb) hbc

/-- A latent-interior path is a directed path. -/
theorem LatentPath.isAncestor (h : LatentPath D L a b) : D.IsAncestor a b := by
  obtain ⟨w, haw, hwb⟩ := h
  have : ReflTransGen D.Adj a w := ReflTransGen.mono (fun _ _ h => h.1) _ _ haw
  exact TransGen.tail' this hwb

/-- Latent-interior paths are monotone in the latent set. -/
theorem LatentPath.mono (hL : L ⊆ L') (h : LatentPath D L a b) : LatentPath D L' a b := by
  obtain ⟨w, haw, hwb⟩ := h
  exact ⟨w, ReflTransGen.mono (fun _ _ h => ⟨h.1, hL h.2⟩) _ _ haw, hwb⟩

/-- With no latent vertices, a latent-interior path is a single edge. -/
@[simp] theorem latentPath_empty : LatentPath D ∅ a b ↔ D.Adj a b := by
  refine ⟨fun ⟨w, haw, hwb⟩ => ?_, latentPath_of_adj⟩
  rcases haw.cases_tail with rfl | ⟨_, _, h⟩
  · exact hwb
  · exact absurd h.2 (Set.notMem_empty _)

@[simp] theorem latentAnc_empty : LatentAnc D ∅ a b ↔ a = b := by
  simp [LatentAnc]

theorem latentAnc_refl (a : V) : LatentAnc D L a a := Or.inl rfl

theorem LatentAnc.mono (hL : L ⊆ L') (h : LatentAnc D L a b) : LatentAnc D L' a b :=
  h.imp_right fun h => ⟨hL h.1, h.2.mono hL⟩

/-- For a latent `a` and an observed `b`, `LatentAnc` is `LatentPath`. -/
theorem latentAnc_iff_of_mem (ha : a ∈ L) (hb : b ∉ L) :
    LatentAnc D L a b ↔ LatentPath D L a b :=
  ⟨fun h => h.elim (fun h => absurd (h ▸ ha) hb) And.right, fun h => Or.inr ⟨ha, h⟩⟩

/-- A `LatentAnc` segment ending at a latent `a`, extended by an edge `a → b`. -/
theorem LatentAnc.tail (h : LatentAnc D L c a) (ha : a ∈ L) (hab : D.Adj a b) :
    LatentAnc D L c b := by
  rcases h with rfl | ⟨hc, hca⟩
  · exact Or.inr ⟨ha, latentPath_of_adj hab⟩
  · exact Or.inr ⟨hc, hca.trans ha (latentPath_of_adj hab)⟩

/-- An edge `a → b` followed by a `LatentAnc` segment from `b` is a latent-interior path. -/
theorem LatentAnc.latentPath_of_adj (hab : D.Adj a b) (h : LatentAnc D L b c) :
    LatentPath D L a c := by
  rcases h with rfl | ⟨hb, hbc⟩
  · exact CausalInference.latentPath_of_adj hab
  · exact LatentPath.head hab hb hbc

/-- Two `LatentAnc` segments from the same vertex to two distinct observed vertices meet at a
latent source. -/
theorem exists_latent_source_of_latentAnc (hu : LatentAnc D L c a) (hv : LatentAnc D L c b)
    (hab : a ≠ b) (ha : a ∉ L) (hb : b ∉ L) :
    ∃ l ∈ L, LatentPath D L l a ∧ LatentPath D L l b := by
  rcases hu with rfl | ⟨hc, hca⟩
  · rcases hv with rfl | ⟨hc, _⟩
    · exact absurd rfl hab
    · exact absurd hc ha
  · rcases hv with rfl | ⟨_, hcb⟩
    · exact absurd hc hb
    · exact ⟨c, hc, hca, hcb⟩

end LatentPath

/-! ### The projection -/

namespace ADMG

/-- The bidirected adjacency of the latent projection, before symmetrization proofs:
`u ≠ v`, both observed, and either a latent source with latent-interior directed paths to `u`
and `v`, or a bidirected edge `a ↔ b` of `G` followed by `LatentAnc` segments `a ⇝ u`, `b ⇝ v`.
-/
def ProjectBiAdj (G : ADMG V) (L : Set V) (u v : V) : Prop :=
  u ≠ v ∧ u ∉ L ∧ v ∉ L ∧
    ((∃ l ∈ L, LatentPath G.directed L l u ∧ LatentPath G.directed L l v) ∨
      ∃ a b, G.bidirected.Adj a b ∧ LatentAnc G.directed L a u ∧ LatentAnc G.directed L b v)

theorem ProjectBiAdj.symm {G : ADMG V} {L : Set V} {u v : V} (h : G.ProjectBiAdj L u v) :
    G.ProjectBiAdj L v u := by
  obtain ⟨huv, hu, hv, ⟨l, hl, hlu, hlv⟩ | ⟨a, b, hab, hau, hbv⟩⟩ := h
  · exact ⟨huv.symm, hv, hu, Or.inl ⟨l, hl, hlv, hlu⟩⟩
  · exact ⟨huv.symm, hv, hu, Or.inr ⟨b, a, hab.symm, hbv, hau⟩⟩

/-- The latent projection of the directed mixed graph `G` with latent set `L`, on the same
vertex type, with every latent vertex isolated. Between observed vertices it has
* `u → v` when `G` has a directed path from `u` to `v` with latent interior;
* `u ↔ v`, for `u ≠ v`, when `G` has a collider-free latent-interior path between `u` and `v`
  with arrowheads at both ends: either a latent `l` with latent-interior directed paths to `u`
  and to `v`, or a bidirected edge `a ↔ b` of `G` with `LatentAnc G.directed L a u` and
  `LatentAnc G.directed L b v`.

`projectBiAdj_iff_exists_path` and `project_directed_adj_iff_exists_path` state both edge kinds
as path criteria. -/
def project (G : ADMG V) (L : Set V) : ADMG V where
  directed := { Adj := fun u v => u ∉ L ∧ v ∉ L ∧ LatentPath G.directed L u v }
  bidirected :=
    { Adj := G.ProjectBiAdj L
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }

variable {G : ADMG V} {L L1 L2 : Set V} {u v w a b : V}

@[simp] theorem project_directed_adj :
    (G.project L).directed.Adj u v ↔ u ∉ L ∧ v ∉ L ∧ LatentPath G.directed L u v := Iff.rfl

@[simp] theorem project_bidirected_adj :
    (G.project L).bidirected.Adj u v ↔ G.ProjectBiAdj L u v := Iff.rfl

/-- Latent vertices are isolated in the projection: directed edges join observed vertices. -/
theorem notMem_of_project_directed_adj (h : (G.project L).directed.Adj u v) : u ∉ L ∧ v ∉ L :=
  ⟨h.1, h.2.1⟩

/-- Latent vertices are isolated in the projection: bidirected edges join observed vertices. -/
theorem notMem_of_project_bidirected_adj (h : (G.project L).bidirected.Adj u v) :
    u ∉ L ∧ v ∉ L :=
  ⟨h.2.1, h.2.2.1⟩

/-- A latent vertex is alone in its district of the projection. -/
theorem district_project_of_mem (hv : v ∈ L) : (G.project L).district v = {v} := by
  ext w
  rw [mem_district, SimpleGraph.reachable_iff_reflTransGen, Set.mem_singleton_iff]
  refine ⟨fun h => ?_, fun h => h ▸ ReflTransGen.refl⟩
  rcases h.cases_head with h | ⟨c, hvc, -⟩
  · exact h.symm
  · exact absurd hv (notMem_of_project_bidirected_adj hvc).1

/-- Directed edges between observed vertices are kept. -/
theorem project_directed_adj_of_adj (hu : u ∉ L) (hv : v ∉ L) (h : G.directed.Adj u v) :
    (G.project L).directed.Adj u v :=
  ⟨hu, hv, latentPath_of_adj h⟩

/-- Bidirected edges between observed vertices are kept. -/
theorem project_bidirected_adj_of_adj (hu : u ∉ L) (hv : v ∉ L) (h : G.bidirected.Adj u v) :
    (G.project L).bidirected.Adj u v :=
  ⟨G.bidirected.ne_of_adj h, hu, hv, Or.inr ⟨u, v, h, Or.inl rfl, Or.inl rfl⟩⟩

/-! ### Acyclicity and ancestors -/

/-- A directed edge of the projection is a directed path of the original graph. -/
theorem isAncestor_of_project_adj (h : (G.project L).directed.Adj u v) : G.IsAncestor u v :=
  h.2.2.isAncestor

/-- An ancestor relation in the projection is one in the original graph. -/
theorem IsAncestor.of_project (h : (G.project L).IsAncestor u v) : G.IsAncestor u v := by
  induction h with
  | single h => exact isAncestor_of_project_adj h
  | tail _ hbc ih => exact Digraph.IsAncestor.trans ih (isAncestor_of_project_adj hbc)

/-- The latent projection of an acyclic graph is acyclic. -/
theorem IsAcyclic.project (hG : G.IsAcyclic) : (G.project L).IsAcyclic :=
  fun v h => hG v (IsAncestor.of_project h)

/-- A directed path of `G` from an observed `u` to `v` splits at its last observed vertex `o`
before `v`: a directed path of the projection from `u` to `o`, then a latent-interior path from
`o` to `v`. -/
theorem exists_last_observed (hu : u ∉ L) (h : G.IsAncestor u v) :
    ∃ o, o ∉ L ∧ ReflTransGen (G.project L).directed.Adj u o ∧ LatentPath G.directed L o v := by
  induction h with
  | single h => exact ⟨u, hu, ReflTransGen.refl, latentPath_of_adj h⟩
  | @tail b c _ hbc ih =>
    obtain ⟨o, ho, huo, hob⟩ := ih
    by_cases hb : b ∈ L
    · exact ⟨o, ho, huo, hob.trans hb (latentPath_of_adj hbc)⟩
    · exact ⟨b, hb, huo.tail ⟨ho, hb, hob⟩, latentPath_of_adj hbc⟩

/-- Ancestor relations among observed vertices are preserved exactly by latent projection. -/
theorem isAncestor_project_iff (hu : u ∉ L) (hv : v ∉ L) :
    (G.project L).IsAncestor u v ↔ G.IsAncestor u v := by
  refine ⟨IsAncestor.of_project, fun h => ?_⟩
  obtain ⟨o, ho, huo, hov⟩ := exists_last_observed hu h
  exact TransGen.tail' huo ⟨ho, hv, hov⟩

/-! ### Projecting out nothing -/

/-- Projecting out no vertex gives the graph back. -/
@[simp] theorem project_empty (G : ADMG V) : G.project ∅ = G := by
  ext u v
  · simp
  · simp only [project_bidirected_adj, ProjectBiAdj]
    constructor
    · rintro ⟨_, _, _, ⟨l, hl, -⟩ | ⟨a, b, hab, hau, hbv⟩⟩
      · exact absurd hl (Set.notMem_empty l)
      · rw [latentAnc_empty] at hau hbv
        subst hau hbv
        exact hab
    · exact fun h => ⟨G.bidirected.ne_of_adj h, Set.notMem_empty u, Set.notMem_empty v,
        Or.inr ⟨u, v, h, Or.inl rfl, Or.inl rfl⟩⟩

/-! ### The path criterion

The definition of `project` lists the two shapes of a collider-free latent-interior path with
arrowheads at both ends. The walks below state the path criterion itself, with colliders defined
from the edge marks, and `projectBiAdj_iff_exists_path` proves that it agrees with the two
shapes; `project_directed_adj_iff_exists_path` is the directed counterpart. -/

/-- `G.LatentTrail L a u w l`: `l` is the list of vertices of a walk in `G` from `u` to `w` in
which every vertex other than the last lies in `L`, no vertex is a collider, and the last step
enters `w` through an arrowhead. A step uses a directed edge in either direction or a
bidirected edge. The flag `a = true` records that the walk arrived at `u` through an arrowhead
at `u`. A collider is a vertex entered and left through arrowheads, so a vertex entered through
an arrowhead can only be left along a directed edge out of it. The constructors are:

* `nil`: the one-vertex walk at `w`, allowed only with flag `true` (an arrowhead at `w`);
* `fwd`: a step along `u → v` from a latent `u`; it leaves `u` through a tail and enters `v`
  through an arrowhead;
* `bwd`: a step along `u ← v` from a latent `u` not entered through an arrowhead; it enters `v`
  through a tail;
* `bi`: a step along `u ↔ v` from a latent `u` not entered through an arrowhead; it enters `v`
  through an arrowhead. -/
inductive LatentTrail (G : ADMG V) (L : Set V) : Bool → V → V → List V → Prop
  | nil {w : V} : LatentTrail G L true w w [w]
  | fwd {a : Bool} {u v w : V} {l : List V} (hu : u ∈ L) (h : G.directed.Adj u v)
      (p : LatentTrail G L true v w l) : LatentTrail G L a u w (u :: l)
  | bwd {u v w : V} {l : List V} (hu : u ∈ L) (h : G.directed.Adj v u)
      (p : LatentTrail G L false v w l) : LatentTrail G L false u w (u :: l)
  | bi {u v w : V} {l : List V} (hu : u ∈ L) (h : G.bidirected.Adj u v)
      (p : LatentTrail G L true v w l) : LatentTrail G L false u w (u :: l)

/-- `G.ProjectionTrail L u w l`: `l` is the list of vertices of a walk from `u` to `w` whose
interior vertices all lie in `L`, with no collider, and with an arrowhead at both ends: the
first step enters `u` through an arrowhead (`u ← v` or `u ↔ v`), and the rest is a
`LatentTrail` from `v`. With `l.Nodup` it is a path. -/
def ProjectionTrail (G : ADMG V) (L : Set V) (u w : V) (l : List V) : Prop :=
  ∃ v l', l = u :: l' ∧
    ((G.directed.Adj v u ∧ G.LatentTrail L false v w l') ∨
      (G.bidirected.Adj u v ∧ G.LatentTrail L true v w l'))

/-- `G.DirectedProjectionTrail L u w l`: `l` is the list of vertices of a directed walk
`u → ⋯ → w` with at least one edge whose interior vertices all lie in `L`. With `l.Nodup` it is
a directed path. -/
def DirectedProjectionTrail (G : ADMG V) (L : Set V) (u w : V) (l : List V) : Prop :=
  ∃ v l', l = u :: l' ∧ G.directed.Adj u v ∧ G.LatentTrail L true v w l'

namespace LatentTrail

variable {a b : Bool} {x y c : V} {l : List V}

/-- Every vertex of a `LatentTrail` other than its last one is latent. -/
theorem mem_of_mem (p : G.LatentTrail L a u w l) (hx : x ∈ l) : x ∈ L ∨ x = w := by
  induction p with
  | nil => exact Or.inr (List.mem_singleton.1 hx)
  | fwd hu _ _ ih | bwd hu _ _ ih | bi hu _ _ ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl hu
    · exact ih hx

/-- The last vertex lies on the walk. -/
theorem end_mem (p : G.LatentTrail L a u w l) : w ∈ l := by
  induction p with
  | nil => exact List.mem_singleton_self _
  | fwd _ _ _ ih | bwd _ _ _ ih | bi _ _ _ ih => exact List.mem_cons_of_mem _ ih

/-- A walk not entered through an arrowhead has a first step, so its first vertex is latent. -/
theorem mem_of_false (p : G.LatentTrail L false u w l) : u ∈ L := by
  cases p with
  | fwd hu _ _ | bwd hu _ _ | bi hu _ _ => exact hu

/-- A walk entered through an arrowhead at `u ≠ w` leaves `u` along a directed edge, so it is
valid whatever the arrival at `u`. -/
theorem of_true (p : G.LatentTrail L true u w l) (h : u ≠ w) (a : Bool) :
    G.LatentTrail L a u w l := by
  cases p with
  | nil => exact absurd rfl h
  | fwd hu huv q => exact .fwd hu huv q

/-- The suffix of a walk from a later occurrence of `x` is a walk from `x`; if the walk was
entered through an arrowhead, so is the suffix. -/
theorem exists_suffix (p : G.LatentTrail L a u w l) (hx : x ∈ l) :
    ∃ b l', l' <:+ l ∧ G.LatentTrail L b x w l' ∧ (a = true → b = true) := by
  induction p with
  | nil =>
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨true, _, List.suffix_refl _, .nil, fun _ => rfl⟩
  | @fwd a u v w l hu h q ih =>
    by_cases hxu : x = u
    · subst hxu
      exact ⟨a, _, List.suffix_refl _, .fwd hu h q, id⟩
    · obtain ⟨b, l', hsuf, hl', hb⟩ := ih ((List.mem_cons.1 hx).resolve_left hxu)
      exact ⟨b, l', hsuf.trans (List.suffix_cons _ _), hl', fun _ => hb rfl⟩
  | @bwd u v w l hu h q ih =>
    by_cases hxu : x = u
    · subst hxu
      exact ⟨false, _, List.suffix_refl _, .bwd hu h q, id⟩
    · obtain ⟨b, l', hsuf, hl', -⟩ := ih ((List.mem_cons.1 hx).resolve_left hxu)
      exact ⟨b, l', hsuf.trans (List.suffix_cons _ _), hl', (fun h => nomatch h)⟩
  | @bi u v w l hu h q ih =>
    by_cases hxu : x = u
    · subst hxu
      exact ⟨false, _, List.suffix_refl _, .bi hu h q, id⟩
    · obtain ⟨b, l', hsuf, hl', -⟩ := ih ((List.mem_cons.1 hx).resolve_left hxu)
      exact ⟨b, l', hsuf.trans (List.suffix_cons _ _), hl', (fun h => nomatch h)⟩

/-- Shortening to a path: a walk ending at an observed `w` contains a walk with the same
endpoints and flag and no repeated vertex. A repeated vertex is latent, and cutting out the loop
between two of its occurrences creates no collider. -/
theorem exists_nodup (p : G.LatentTrail L a u w l) (hw : w ∉ L) :
    ∃ l', l'.Sublist l ∧ G.LatentTrail L a u w l' ∧ l'.Nodup := by
  induction p with
  | nil => exact ⟨_, List.Sublist.refl _, .nil, List.nodup_singleton _⟩
  | @fwd a u v w l hu h q ih =>
    obtain ⟨l', hsub, q', hnd⟩ := ih hw
    by_cases hul : u ∈ l'
    · obtain ⟨b, l'', hsuf, q'', hb⟩ := q'.exists_suffix hul
      obtain rfl := hb rfl
      exact ⟨l'', (hsuf.sublist.trans hsub).trans (List.sublist_cons_self _ _),
        q''.of_true (fun h => hw (h ▸ hu)) a, hnd.sublist hsuf.sublist⟩
    · exact ⟨u :: l', hsub.cons_cons u, .fwd hu h q', List.nodup_cons.2 ⟨hul, hnd⟩⟩
  | @bwd u v w l hu h q ih =>
    obtain ⟨l', hsub, q', hnd⟩ := ih hw
    by_cases hul : u ∈ l'
    · obtain ⟨b, l'', hsuf, q'', -⟩ := q'.exists_suffix hul
      refine ⟨l'', (hsuf.sublist.trans hsub).trans (List.sublist_cons_self _ _), ?_,
        hnd.sublist hsuf.sublist⟩
      cases b
      · exact q''
      · exact q''.of_true (fun h => hw (h ▸ hu)) false
    · exact ⟨u :: l', hsub.cons_cons u, .bwd hu h q', List.nodup_cons.2 ⟨hul, hnd⟩⟩
  | @bi u v w l hu h q ih =>
    obtain ⟨l', hsub, q', hnd⟩ := ih hw
    by_cases hul : u ∈ l'
    · obtain ⟨b, l'', hsuf, q'', -⟩ := q'.exists_suffix hul
      refine ⟨l'', (hsuf.sublist.trans hsub).trans (List.sublist_cons_self _ _), ?_,
        hnd.sublist hsuf.sublist⟩
      cases b
      · exact q''
      · exact q''.of_true (fun h => hw (h ▸ hu)) false
    · exact ⟨u :: l', hsub.cons_cons u, .bi hu h q', List.nodup_cons.2 ⟨hul, hnd⟩⟩

/-- The shape of a `LatentTrail`. Entered through an arrowhead, it is a `LatentAnc` segment.
Otherwise it runs backward along directed edges to a latent vertex `c` and then either forward
to `w`, or across a bidirected edge `c ↔ d` and forward from `d` to `w`. -/
theorem shape (p : G.LatentTrail L a u w l) :
    (a = true → LatentAnc G.directed L u w) ∧
    (a = false → (∃ c ∈ L, LatentAnc G.directed L c u ∧ LatentPath G.directed L c w) ∨
      ∃ c d, G.bidirected.Adj c d ∧ LatentAnc G.directed L c u ∧
        LatentAnc G.directed L d w) := by
  induction p with
  | nil => exact ⟨fun _ => latentAnc_refl _, (fun h => nomatch h)⟩
  | fwd hu h _ ih =>
    have hp := (ih.1 rfl).latentPath_of_adj h
    exact ⟨fun _ => Or.inr ⟨hu, hp⟩, fun _ => Or.inl ⟨_, hu, latentAnc_refl _, hp⟩⟩
  | bwd _ hvu q ih =>
    refine ⟨(fun h => nomatch h), fun _ => ?_⟩
    have hv := q.mem_of_false
    rcases ih.2 rfl with ⟨c, hc, hcv, hcw⟩ | ⟨c, d, hcd, hcv, hdw⟩
    · exact Or.inl ⟨c, hc, hcv.tail hv hvu, hcw⟩
    · exact Or.inr ⟨c, d, hcd, hcv.tail hv hvu, hdw⟩
  | bi _ huv _ ih =>
    exact ⟨(fun h => nomatch h),
      fun _ => Or.inr ⟨_, _, huv, latentAnc_refl _, ih.1 rfl⟩⟩

/-- A latent-interior directed path from a latent `c` is a `LatentTrail` from `c`, for either
flag. -/
theorem of_latentPath (hc : c ∈ L) (h : LatentPath G.directed L c w) (a : Bool) :
    ∃ l, G.LatentTrail L a c w l := by
  obtain ⟨y, hcy, hyw⟩ := h
  revert hc a
  induction hcy using ReflTransGen.head_induction_on with
  | refl => exact fun hc _ => ⟨_, .fwd hc hyw .nil⟩
  | head hcd _ ih =>
    intro hc _
    obtain ⟨l, hl⟩ := ih hcd.2 true
    exact ⟨_, .fwd hc hcd.1 hl⟩

/-- Prepending backward steps: if `c → ⋯ → y` is a directed path into latent vertices, a walk
from `c` not entered through an arrowhead extends to one from `y`. -/
theorem of_reflTransGen_latentStep
    (hcy : ReflTransGen (latentStepDigraph G.directed L).Adj c y)
    (p : G.LatentTrail L false c w l) : ∃ l', G.LatentTrail L false y w l' := by
  induction hcy with
  | refl => exact ⟨l, p⟩
  | tail _ hyz ih =>
    obtain ⟨l', hl'⟩ := ih
    exact ⟨_, .bwd hyz.2 hyz.1 hl'⟩

end LatentTrail

variable {l : List V}

/-- A walk satisfying the path criterion between distinct observed vertices gives a bidirected
edge of the projection. -/
theorem projectBiAdj_of_projectionTrail (huw : u ≠ w) (hu : u ∉ L) (hw : w ∉ L)
    (h : G.ProjectionTrail L u w l) : G.ProjectBiAdj L u w := by
  obtain ⟨v, l', -, ⟨hvu, p⟩ | ⟨huv, p⟩⟩ := h
  · have hv := p.mem_of_false
    refine ⟨huw, hu, hw, ?_⟩
    rcases p.shape.2 rfl with ⟨c, hc, hcv, hcw⟩ | ⟨c, d, hcd, hcv, hdw⟩
    · exact Or.inl ⟨c, hc, (latentAnc_iff_of_mem hc hu).1 (hcv.tail hv hvu), hcw⟩
    · exact Or.inr ⟨c, d, hcd, hcv.tail hv hvu, hdw⟩
  · exact ⟨huw, hu, hw, Or.inr ⟨u, v, huv, latentAnc_refl u, p.shape.1 rfl⟩⟩

/-- Each of the two shapes of a projected bidirected edge is a walk satisfying the path
criterion. -/
theorem exists_projectionTrail_of_projectBiAdj (h : G.ProjectBiAdj L u w) :
    ∃ l, G.ProjectionTrail L u w l := by
  obtain ⟨-, -, -, ⟨c, hc, ⟨y, hcy, hyu⟩, hcw⟩ | ⟨c, d, hcd, hcu, hdw⟩⟩ := h
  · obtain ⟨l, hl⟩ := LatentTrail.of_latentPath hc hcw false
    obtain ⟨l', hl'⟩ := LatentTrail.of_reflTransGen_latentStep hcy hl
    exact ⟨_, y, l', rfl, Or.inl ⟨hyu, hl'⟩⟩
  · obtain ⟨ld, hd⟩ : ∃ ld, G.LatentTrail L true d w ld := by
      rcases hdw with rfl | ⟨hd, hdw⟩
      · exact ⟨_, .nil⟩
      · exact LatentTrail.of_latentPath hd hdw true
    rcases hcu with rfl | ⟨hc, y, hcy, hyu⟩
    · exact ⟨_, d, ld, rfl, Or.inr ⟨hcd, hd⟩⟩
    · obtain ⟨l', hl'⟩ := LatentTrail.of_reflTransGen_latentStep hcy (.bi hc hcd hd)
      exact ⟨_, y, l', rfl, Or.inl ⟨hyu, hl'⟩⟩

/-- Path criterion for the bidirected edges of the projection, with walks: `u ↔ w` in
`G.project L` exactly when `u ≠ w` are observed and joined by a walk with latent interior, no
collider, and arrowheads at both ends. -/
theorem projectBiAdj_iff_exists_trail :
    G.ProjectBiAdj L u w ↔ u ≠ w ∧ u ∉ L ∧ w ∉ L ∧ ∃ l, G.ProjectionTrail L u w l :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, exists_projectionTrail_of_projectBiAdj h⟩,
    fun ⟨huw, hu, hw, _, hl⟩ => projectBiAdj_of_projectionTrail huw hu hw hl⟩

/-- A walk satisfying the path criterion between observed `u ≠ w` can be shortened to a path. -/
theorem ProjectionTrail.exists_nodup (hu : u ∉ L) (hw : w ∉ L) (huw : u ≠ w)
    (h : G.ProjectionTrail L u w l) : ∃ l', G.ProjectionTrail L u w l' ∧ l'.Nodup := by
  obtain ⟨v, l, rfl, h⟩ := h
  have key : ∀ {a : Bool}, G.LatentTrail L a v w l →
      ∃ l'', G.LatentTrail L a v w l'' ∧ (u :: l'').Nodup := by
    intro a p
    obtain ⟨l'', -, p'', hnd⟩ := p.exists_nodup hw
    refine ⟨l'', p'', List.nodup_cons.2 ⟨fun hul => ?_, hnd⟩⟩
    rcases p''.mem_of_mem hul with h | h
    · exact hu h
    · exact huw h
  rcases h with ⟨hvu, p⟩ | ⟨huv, p⟩
  · obtain ⟨l'', p'', hnd⟩ := key p
    exact ⟨_, ⟨v, l'', rfl, Or.inl ⟨hvu, p''⟩⟩, hnd⟩
  · obtain ⟨l'', p'', hnd⟩ := key p
    exact ⟨_, ⟨v, l'', rfl, Or.inr ⟨huv, p''⟩⟩, hnd⟩

/-- The endpoints of a path satisfying the criterion are distinct. -/
theorem ProjectionTrail.ne_of_nodup (h : G.ProjectionTrail L u w l) (hl : l.Nodup) : u ≠ w := by
  obtain ⟨v, l', rfl, ⟨-, p⟩ | ⟨-, p⟩⟩ := h <;>
  exact fun huw => (List.nodup_cons.1 hl).1 (huw ▸ p.end_mem)

/-- Path criterion for the bidirected edges of the projection: `u ↔ w` in `G.project L` exactly
when `u` and `w` are observed and joined by a path (no repeated vertex) with latent interior, no
collider, and arrowheads at both ends. -/
theorem projectBiAdj_iff_exists_path :
    G.ProjectBiAdj L u w ↔ u ∉ L ∧ w ∉ L ∧ ∃ l, G.ProjectionTrail L u w l ∧ l.Nodup := by
  rw [projectBiAdj_iff_exists_trail]
  constructor
  · rintro ⟨huw, hu, hw, l, hl⟩
    exact ⟨hu, hw, hl.exists_nodup hu hw huw⟩
  · rintro ⟨hu, hw, l, hl, hnd⟩
    exact ⟨hl.ne_of_nodup hnd, hu, hw, l, hl⟩

/-- Path criterion for latent-interior directed paths, with walks. -/
theorem latentPath_iff_exists_directedProjectionTrail :
    LatentPath G.directed L u w ↔ ∃ l, G.DirectedProjectionTrail L u w l := by
  constructor
  · rintro ⟨y, huy, hyw⟩
    rcases huy.cases_head with rfl | ⟨v, huv, hvy⟩
    · exact ⟨_, w, [w], rfl, hyw, .nil⟩
    · obtain ⟨l, hl⟩ := LatentTrail.of_latentPath huv.2 ⟨y, hvy, hyw⟩ true
      exact ⟨_, v, l, rfl, huv.1, hl⟩
  · rintro ⟨l, v, l', -, huv, p⟩
    exact (p.shape.1 rfl).latentPath_of_adj huv

/-- Path criterion for latent-interior directed paths between distinct observed vertices: such a
path exists exactly when a directed path with no repeated vertex and latent interior does. -/
theorem latentPath_iff_exists_nodup (huw : u ≠ w) (hu : u ∉ L) (hw : w ∉ L) :
    LatentPath G.directed L u w ↔ ∃ l, G.DirectedProjectionTrail L u w l ∧ l.Nodup := by
  rw [latentPath_iff_exists_directedProjectionTrail]
  refine ⟨fun ⟨_, v, l, hl, huv, p⟩ => ?_, fun ⟨l, hl, _⟩ => ⟨l, hl⟩⟩
  obtain ⟨l', -, p', hnd⟩ := p.exists_nodup hw
  refine ⟨_, ⟨v, l', rfl, huv, p'⟩, List.nodup_cons.2 ⟨fun hul => ?_, hnd⟩⟩
  rcases p'.mem_of_mem hul with h | h
  · exact hu h
  · exact huw h

/-- Path criterion for the directed edges of the projection: for `u ≠ w`, `u → w` in
`G.project L` exactly when `u` and `w` are observed and joined by a directed path (no repeated
vertex) whose interior vertices are latent. -/
theorem project_directed_adj_iff_exists_path (huw : u ≠ w) :
    (G.project L).directed.Adj u w ↔
      u ∉ L ∧ w ∉ L ∧ ∃ l, G.DirectedProjectionTrail L u w l ∧ l.Nodup :=
  ⟨fun ⟨hu, hw, h⟩ => ⟨hu, hw, (latentPath_iff_exists_nodup huw hu hw).1 h⟩,
    fun ⟨hu, hw, h⟩ => ⟨hu, hw, (latentPath_iff_exists_nodup huw hu hw).2 h⟩⟩

end ADMG

/-! ### Two-stage projection -/

section TwoStage

open ADMG

variable {G : ADMG V} {L1 L2 : Set V} {u v a b : V}

/-- A latent-interior path in a projection starts and ends at observed vertices. -/
theorem LatentPath.notMem_of_project {L L' : Set V}
    (h : LatentPath (G.project L).directed L' a b) : a ∉ L ∧ b ∉ L := by
  obtain ⟨w, haw, hwb⟩ := h
  refine ⟨?_, hwb.2.1⟩
  rcases haw.cases_head with rfl | ⟨c, hac, _⟩
  · exact hwb.1
  · exact hac.1.1

/-- A latent-interior path of the second stage is one of the combined projection. -/
theorem LatentPath.of_project (h : LatentPath (G.project L1).directed L2 a b) :
    LatentPath G.directed (L1 ∪ L2) a b := by
  obtain ⟨w, haw, hwb⟩ := h
  have hstep : ReflTransGen (latentStepDigraph G.directed (L1 ∪ L2)).Adj a w := by
    clear hwb
    induction haw with
    | refl => exact ReflTransGen.refl
    | tail _ hcd ih =>
      exact ih.trans ((hcd.1.2.2.mono Set.subset_union_left).reflTransGen
        (Set.mem_union_right _ hcd.2))
  exact LatentPath.of_reflTransGen hstep (hwb.2.2.mono Set.subset_union_left)

/-- A latent-interior path of `G` (latent set `L1 ∪ L2`) between vertices outside `L1` is a
latent-interior path of the first-stage projection (latent set `L2`). -/
theorem LatentPath.project_of_notMem (ha : a ∉ L1) (hb : b ∉ L1)
    (h : LatentPath G.directed (L1 ∪ L2) a b) : LatentPath (G.project L1).directed L2 a b := by
  obtain ⟨w, haw, hwb⟩ := h
  have key : ∃ o, o ∉ L1 ∧ ReflTransGen (latentStepDigraph (G.project L1).directed L2).Adj a o ∧
      ReflTransGen (latentStepDigraph G.directed L1).Adj o w := by
    clear hwb
    induction haw with
    | refl => exact ⟨a, ha, ReflTransGen.refl, ReflTransGen.refl⟩
    | @tail c d _ hcd ih =>
      obtain ⟨o, ho, hao, hoc⟩ := ih
      by_cases hd : d ∈ L1
      · exact ⟨o, ho, hao, hoc.tail ⟨hcd.1, hd⟩⟩
      · have hd2 : d ∈ L2 := hcd.2.resolve_left hd
        exact ⟨d, hd, hao.tail ⟨⟨ho, hd, c, hoc, hcd.1⟩, hd2⟩, ReflTransGen.refl⟩
  obtain ⟨o, ho, hao, how⟩ := key
  exact ⟨o, hao, ho, hb, w, how, hwb⟩

/-- A latent-interior path of `G` from a vertex of `L1` to a vertex outside `L1` first reaches a
vertex `y` outside `L1` through `L1`, then continues to its end in the first-stage
projection. -/
theorem LatentPath.exists_split_of_mem (ha : a ∈ L1) (hb : b ∉ L1)
    (h : LatentPath G.directed (L1 ∪ L2) a b) :
    ∃ y, y ∉ L1 ∧ LatentPath G.directed L1 a y ∧ LatentAnc (G.project L1).directed L2 y b := by
  obtain ⟨w, haw, hwb⟩ := h
  induction haw using ReflTransGen.head_induction_on with
  | refl => exact ⟨b, hb, latentPath_of_adj hwb, Or.inl rfl⟩
  | @head a c hac hcw ih =>
    by_cases hc : c ∈ L1
    · obtain ⟨y, hy, hcy, hyb⟩ := ih hc
      exact ⟨y, hy, hcy.head hac.1 hc, hyb⟩
    · refine ⟨c, hc, latentPath_of_adj hac.1, Or.inr ⟨hac.2.resolve_left hc, ?_⟩⟩
      exact LatentPath.project_of_notMem hc hb ⟨w, hcw, hwb⟩

/-- Splitting a `LatentAnc` segment of `G` (latent set `L1 ∪ L2`) that ends at an observed
vertex into a first-stage segment and a second-stage segment. -/
theorem LatentAnc.exists_split (hb : b ∉ L1 ∪ L2) (h : LatentAnc G.directed (L1 ∪ L2) a b) :
    ∃ y, y ∉ L1 ∧ LatentAnc G.directed L1 a y ∧ LatentAnc (G.project L1).directed L2 y b := by
  have hb1 : b ∉ L1 := fun h => hb (Set.mem_union_left _ h)
  rcases h with rfl | ⟨ha, hab⟩
  · exact ⟨a, hb1, Or.inl rfl, Or.inl rfl⟩
  · by_cases ha1 : a ∈ L1
    · obtain ⟨y, hy, hay, hyb⟩ := hab.exists_split_of_mem ha1 hb1
      exact ⟨y, hy, Or.inr ⟨ha1, hay⟩, hyb⟩
    · exact ⟨a, ha1, Or.inl rfl,
        Or.inr ⟨ha.resolve_left ha1, LatentPath.project_of_notMem ha1 hb1 hab⟩⟩

/-- Composing a first-stage segment with a second-stage segment. -/
theorem LatentAnc.of_project {y : V} (hay : LatentAnc G.directed L1 a y)
    (hyb : LatentAnc (G.project L1).directed L2 y b) : LatentAnc G.directed (L1 ∪ L2) a b := by
  rcases hay with rfl | ⟨ha, hay⟩
  · exact hyb.imp_right fun h => ⟨Set.mem_union_right _ h.1, h.2.of_project⟩
  · refine Or.inr ⟨Set.mem_union_left _ ha, ?_⟩
    rcases hyb with rfl | ⟨hy, hyb⟩
    · exact hay.mono Set.subset_union_left
    · exact (hay.mono Set.subset_union_left).trans (Set.mem_union_right _ hy) hyb.of_project

/-- Two first-stage endpoints `y₁`, `y₂` that are joined in the first-stage projection whenever
they differ, followed by second-stage segments to distinct observed `u` and `v`, give a
bidirected edge `u ↔ v` of the two-stage projection. -/
theorem projectBiAdj_of_split {y₁ y₂ : V} (huv : u ≠ v) (hu : u ∉ L2) (hv : v ∉ L2)
    (hy : y₁ ≠ y₂ → (G.project L1).bidirected.Adj y₁ y₂)
    (h₁ : LatentAnc (G.project L1).directed L2 y₁ u)
    (h₂ : LatentAnc (G.project L1).directed L2 y₂ v) :
    (G.project L1).ProjectBiAdj L2 u v := by
  refine ⟨huv, hu, hv, ?_⟩
  by_cases hne : y₁ = y₂
  · subst hne
    exact Or.inl (exists_latent_source_of_latentAnc h₁ h₂ huv hu hv)
  · exact Or.inr ⟨y₁, y₂, hy hne, h₁, h₂⟩

end TwoStage

namespace ADMG

variable {V : Type*}

/-- Projection in two stages equals projection in one stage: projecting out `L1` and then `L2`
is projecting out `L1 ∪ L2`. -/
theorem project_project (G : ADMG V) (L1 L2 : Set V) :
    (G.project L1).project L2 = G.project (L1 ∪ L2) := by
  ext u v
  · simp only [project_directed_adj, Set.mem_union, not_or]
    constructor
    · rintro ⟨hu2, hv2, h⟩
      have h1 := h.notMem_of_project
      exact ⟨⟨h1.1, hu2⟩, ⟨h1.2, hv2⟩, h.of_project⟩
    · rintro ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩, h⟩
      exact ⟨hu2, hv2, LatentPath.project_of_notMem hu1 hv1 h⟩
  · simp only [project_bidirected_adj]
    constructor
    · rintro ⟨huv, hu2, hv2, ⟨l, hl, hlu, hlv⟩ | ⟨a, b, hab, hau, hbv⟩⟩
      · refine ⟨huv, fun h => h.elim hlu.notMem_of_project.2 hu2,
          fun h => h.elim hlv.notMem_of_project.2 hv2, Or.inl ?_⟩
        exact ⟨l, Set.mem_union_right _ hl, hlu.of_project, hlv.of_project⟩
      · obtain ⟨-, ha1, hb1, hfork⟩ := hab
        have hu1 : u ∉ L1 := by
          rcases hau with rfl | ⟨_, hau⟩
          · exact ha1
          · exact hau.notMem_of_project.2
        have hv1 : v ∉ L1 := by
          rcases hbv with rfl | ⟨_, hbv⟩
          · exact hb1
          · exact hbv.notMem_of_project.2
        have hu : u ∉ L1 ∪ L2 := fun h => h.elim hu1 hu2
        have hv : v ∉ L1 ∪ L2 := fun h => h.elim hv1 hv2
        refine ⟨huv, hu, hv, ?_⟩
        rcases hfork with ⟨l, hl, hla, hlb⟩ | ⟨a', b', hab', ha'a, hb'b⟩
        · have hlu := LatentAnc.of_project (Or.inr ⟨hl, hla⟩) hau
          have hlv := LatentAnc.of_project (Or.inr ⟨hl, hlb⟩) hbv
          have hlL : l ∈ L1 ∪ L2 := Set.mem_union_left _ hl
          exact Or.inl ⟨l, hlL, (latentAnc_iff_of_mem hlL hu).1 hlu,
            (latentAnc_iff_of_mem hlL hv).1 hlv⟩
        · exact Or.inr ⟨a', b', hab', ha'a.of_project hau, hb'b.of_project hbv⟩
    · rintro ⟨huv, hu, hv, ⟨l, hl, hlu, hlv⟩ | ⟨a, b, hab, hau, hbv⟩⟩
      · have hu1 : u ∉ L1 := fun h => hu (Set.mem_union_left _ h)
        have hv1 : v ∉ L1 := fun h => hv (Set.mem_union_left _ h)
        have hu2 : u ∉ L2 := fun h => hu (Set.mem_union_right _ h)
        have hv2 : v ∉ L2 := fun h => hv (Set.mem_union_right _ h)
        by_cases hl1 : l ∈ L1
        · obtain ⟨y₁, hy₁, hly₁, hy₁u⟩ := hlu.exists_split_of_mem hl1 hu1
          obtain ⟨y₂, hy₂, hly₂, hy₂v⟩ := hlv.exists_split_of_mem hl1 hv1
          exact projectBiAdj_of_split huv hu2 hv2
            (fun hne => ⟨hne, hy₁, hy₂, Or.inl ⟨l, hl1, hly₁, hly₂⟩⟩) hy₁u hy₂v
        · have hl2 : l ∈ L2 := hl.resolve_left hl1
          exact ⟨huv, hu2, hv2, Or.inl ⟨l, hl2, LatentPath.project_of_notMem hl1 hu1 hlu,
            LatentPath.project_of_notMem hl1 hv1 hlv⟩⟩
      · have hu2 : u ∉ L2 := fun h => hu (Set.mem_union_right _ h)
        have hv2 : v ∉ L2 := fun h => hv (Set.mem_union_right _ h)
        obtain ⟨y₁, hy₁, hay₁, hy₁u⟩ := hau.exists_split hu
        obtain ⟨y₂, hy₂, hby₂, hy₂v⟩ := hbv.exists_split hv
        exact projectBiAdj_of_split huv hu2 hv2
          (fun hne => ⟨hne, hy₁, hy₂, Or.inr ⟨a, b, hab, hay₁, hby₂⟩⟩) hy₁u hy₂v

end ADMG

/-! ### Latent projection of a DAG -/

/-- The latent projection of the directed graph `D` with latent set `L`: an ADMG on the same
vertex type, with every latent vertex isolated. Between observed vertices it has `u → v` when
`D` has a directed path from `u` to `v` with latent interior, and `u ↔ v` (for `u ≠ v`) when
some latent `l` has directed latent-interior paths to both `u` and `v`
(`latentProjection_bidirected_adj`). -/
def latentProjection (D : Digraph V) (L : Set V) : ADMG V := (ADMG.ofDigraph D).project L

section DAG

variable {D : Digraph V} {L L1 L2 : Set V} {u v : V}

@[simp] theorem latentProjection_directed_adj :
    (latentProjection D L).directed.Adj u v ↔ u ∉ L ∧ v ∉ L ∧ LatentPath D L u v := Iff.rfl

/-- In the latent projection of a DAG, `u ↔ v` exactly when `u` and `v` are distinct observed
vertices with a common latent source `l` reaching each by a directed latent-interior path. -/
@[simp] theorem latentProjection_bidirected_adj :
    (latentProjection D L).bidirected.Adj u v ↔
      u ≠ v ∧ u ∉ L ∧ v ∉ L ∧ ∃ l ∈ L, LatentPath D L l u ∧ LatentPath D L l v := by
  simp [latentProjection, ADMG.ProjectBiAdj]

/-- The latent projection of a DAG is acyclic. -/
theorem latentProjection_isAcyclic (hD : D.IsAcyclic) : (latentProjection D L).IsAcyclic :=
  ADMG.IsAcyclic.project hD

/-- For observed `u` and `v`, `u` is an ancestor of `v` in the latent projection exactly when it
is in the DAG. -/
theorem isAncestor_latentProjection_iff (hu : u ∉ L) (hv : v ∉ L) :
    (latentProjection D L).IsAncestor u v ↔ D.IsAncestor u v :=
  ADMG.isAncestor_project_iff hu hv

/-- Projecting out no vertex gives back the DAG, with no bidirected edges. -/
@[simp] theorem latentProjection_empty (D : Digraph V) :
    latentProjection D ∅ = ADMG.ofDigraph D :=
  ADMG.project_empty _

/-- Two-stage latent projection of a DAG: projecting out `L1` and then `L2` is projecting out
`L1 ∪ L2`. -/
theorem latentProjection_project (D : Digraph V) (L1 L2 : Set V) :
    (latentProjection D L1).project L2 = latentProjection D (L1 ∪ L2) :=
  ADMG.project_project _ L1 L2

end DAG

/-! ### Projection commutes with intervention

For a set `X` of observed vertices, cutting the edges into `X` (or out of `X`) before or after
projecting out `L` gives the same graph. A latent-interior path meets `X` at most at its
endpoints, since its interior is latent. -/

section Intervention

variable {D : Digraph V} {L X : Set V} {a b : V}

/-- Removing the edges into a set of observed vertices does not change the latent steps. -/
theorem latentStepDigraph_deleteIncoming (hXL : Disjoint X L) :
    latentStepDigraph (D.deleteIncoming X) L = latentStepDigraph D L := by
  ext c d
  simp only [latentStepDigraph_adj, Digraph.deleteIncoming_adj]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, Set.disjoint_right.1 hXL h.2⟩, h.2⟩⟩

/-- For `X` disjoint from `L`, a latent-interior path survives the removal of the edges into
`X` exactly when it does not end in `X`. -/
theorem latentPath_deleteIncoming_iff (hXL : Disjoint X L) :
    LatentPath (D.deleteIncoming X) L a b ↔ LatentPath D L a b ∧ b ∉ X := by
  simp only [LatentPath, latentStepDigraph_deleteIncoming hXL, Digraph.deleteIncoming_adj]
  constructor
  · rintro ⟨w, hw, hwb, hb⟩
    exact ⟨⟨w, hw, hwb⟩, hb⟩
  · rintro ⟨⟨w, hw, hwb⟩, hb⟩
    exact ⟨w, hw, hwb, hb⟩

/-- For `X` disjoint from `L`, a `LatentAnc` segment starting outside `X` survives the removal
of the edges into `X` exactly when it does not end in `X`. -/
theorem latentAnc_deleteIncoming_iff (hXL : Disjoint X L) :
    (a ∉ X ∧ LatentAnc (D.deleteIncoming X) L a b) ↔ LatentAnc D L a b ∧ b ∉ X := by
  constructor
  · rintro ⟨ha, rfl | ⟨haL, h⟩⟩
    · exact ⟨Or.inl rfl, ha⟩
    · obtain ⟨h, hb⟩ := (latentPath_deleteIncoming_iff hXL).1 h
      exact ⟨Or.inr ⟨haL, h⟩, hb⟩
  · rintro ⟨rfl | ⟨haL, h⟩, hb⟩
    · exact ⟨hb, Or.inl rfl⟩
    · exact ⟨Set.disjoint_right.1 hXL haL,
        Or.inr ⟨haL, (latentPath_deleteIncoming_iff hXL).2 ⟨h, hb⟩⟩⟩

/-- For `X` disjoint from `L`, a latent-interior path survives the removal of the edges out of
`X` exactly when it does not start in `X`. -/
theorem latentPath_deleteOutgoing_iff (hXL : Disjoint X L) :
    LatentPath (D.deleteOutgoing X) L a b ↔ LatentPath D L a b ∧ a ∉ X := by
  constructor
  · rintro ⟨w, haw, hwb⟩
    refine ⟨⟨w, ReflTransGen.mono (fun _ _ h => ⟨h.1.1, h.2⟩) _ _ haw, hwb.1⟩, ?_⟩
    rcases haw.cases_head with rfl | ⟨c, hac, -⟩
    · exact hwb.2
    · exact hac.1.2
  · rintro ⟨⟨w, haw, hwb⟩, ha⟩
    have key : ∀ c, ReflTransGen (latentStepDigraph D L).Adj c w → c ∉ X →
        ReflTransGen (latentStepDigraph (D.deleteOutgoing X) L).Adj c w ∧ w ∉ X := by
      intro c hcw
      induction hcw using ReflTransGen.head_induction_on with
      | refl => exact fun hc => ⟨ReflTransGen.refl, hc⟩
      | head hcd _ ih =>
        intro hc
        obtain ⟨h1, h2⟩ := ih (Set.disjoint_right.1 hXL hcd.2)
        exact ⟨ReflTransGen.head ⟨⟨hcd.1, hc⟩, hcd.2⟩ h1, h2⟩
    obtain ⟨h1, h2⟩ := key a haw ha
    exact ⟨w, h1, hwb, h2⟩

/-- For `X` disjoint from `L`, removing the edges out of `X` does not change `LatentAnc`. -/
theorem latentAnc_deleteOutgoing_iff (hXL : Disjoint X L) :
    LatentAnc (D.deleteOutgoing X) L a b ↔ LatentAnc D L a b := by
  unfold LatentAnc
  refine or_congr_right (and_congr_right fun ha => ?_)
  rw [latentPath_deleteOutgoing_iff hXL]
  exact and_iff_left (Set.disjoint_right.1 hXL ha)

end Intervention

namespace ADMG

variable {L X : Set V}

/-- Latent projection commutes with `do(X)` for observed `X`: removing the edges into `X` after
projecting is the same as projecting after removing them. -/
theorem project_deleteIncoming (G : ADMG V) (hXL : Disjoint X L) :
    (G.project L).deleteIncoming X = (G.deleteIncoming X).project L := by
  ext u v
  · simp only [deleteIncoming_directed, Digraph.deleteIncoming_adj, project_directed_adj,
      latentPath_deleteIncoming_iff hXL]
    tauto
  · change G.ProjectBiAdj L u v ∧ u ∈ Xᶜ ∧ v ∈ Xᶜ ↔ (G.deleteIncoming X).ProjectBiAdj L u v
    constructor
    · rintro ⟨⟨huv, hu, hv, ⟨l, hl, hlu, hlv⟩ | ⟨a, b, hab, hau, hbv⟩⟩, huX, hvX⟩
      · exact ⟨huv, hu, hv, Or.inl ⟨l, hl, (latentPath_deleteIncoming_iff hXL).2 ⟨hlu, huX⟩,
          (latentPath_deleteIncoming_iff hXL).2 ⟨hlv, hvX⟩⟩⟩
      · obtain ⟨haX, hau'⟩ := (latentAnc_deleteIncoming_iff hXL).2 ⟨hau, huX⟩
        obtain ⟨hbX, hbv'⟩ := (latentAnc_deleteIncoming_iff hXL).2 ⟨hbv, hvX⟩
        exact ⟨huv, hu, hv, Or.inr ⟨a, b, ⟨hab, haX, hbX⟩, hau', hbv'⟩⟩
    · rintro ⟨huv, hu, hv, ⟨l, hl, hlu, hlv⟩ | ⟨a, b, ⟨hab, haX, hbX⟩, hau, hbv⟩⟩
      · obtain ⟨hlu, huX⟩ := (latentPath_deleteIncoming_iff hXL).1 hlu
        obtain ⟨hlv, hvX⟩ := (latentPath_deleteIncoming_iff hXL).1 hlv
        exact ⟨⟨huv, hu, hv, Or.inl ⟨l, hl, hlu, hlv⟩⟩, huX, hvX⟩
      · obtain ⟨hau, huX⟩ := (latentAnc_deleteIncoming_iff hXL).1 ⟨haX, hau⟩
        obtain ⟨hbv, hvX⟩ := (latentAnc_deleteIncoming_iff hXL).1 ⟨hbX, hbv⟩
        exact ⟨⟨huv, hu, hv, Or.inr ⟨a, b, hab, hau, hbv⟩⟩, huX, hvX⟩

/-- Latent projection commutes with removing the edges out of an observed set `X`. -/
theorem project_deleteOutgoing (G : ADMG V) (hXL : Disjoint X L) :
    (G.project L).deleteOutgoing X = (G.deleteOutgoing X).project L := by
  ext u v
  · simp only [deleteOutgoing_directed, Digraph.deleteOutgoing_adj, project_directed_adj,
      latentPath_deleteOutgoing_iff hXL]
    tauto
  · change G.ProjectBiAdj L u v ↔ (G.deleteOutgoing X).ProjectBiAdj L u v
    constructor
    · rintro ⟨huv, hu, hv, ⟨l, hl, hlu, hlv⟩ | ⟨a, b, hab, hau, hbv⟩⟩
      · have hlX := Set.disjoint_right.1 hXL hl
        exact ⟨huv, hu, hv, Or.inl ⟨l, hl, (latentPath_deleteOutgoing_iff hXL).2 ⟨hlu, hlX⟩,
          (latentPath_deleteOutgoing_iff hXL).2 ⟨hlv, hlX⟩⟩⟩
      · exact ⟨huv, hu, hv, Or.inr ⟨a, b, hab, (latentAnc_deleteOutgoing_iff hXL).2 hau,
          (latentAnc_deleteOutgoing_iff hXL).2 hbv⟩⟩
    · rintro ⟨huv, hu, hv, ⟨l, hl, hlu, hlv⟩ | ⟨a, b, hab, hau, hbv⟩⟩
      · exact ⟨huv, hu, hv, Or.inl ⟨l, hl, ((latentPath_deleteOutgoing_iff hXL).1 hlu).1,
          ((latentPath_deleteOutgoing_iff hXL).1 hlv).1⟩⟩
      · exact ⟨huv, hu, hv, Or.inr ⟨a, b, hab, (latentAnc_deleteOutgoing_iff hXL).1 hau,
          (latentAnc_deleteOutgoing_iff hXL).1 hbv⟩⟩

end ADMG

/-- Latent projection of a DAG commutes with `do(X)` for observed `X`. -/
theorem latentProjection_deleteIncoming (D : Digraph V) {L X : Set V} (hXL : Disjoint X L) :
    (latentProjection D L).deleteIncoming X = latentProjection (D.deleteIncoming X) L := by
  rw [latentProjection, latentProjection, ADMG.project_deleteIncoming _ hXL,
    ADMG.deleteIncoming_ofDigraph]

/-- Latent projection of a DAG commutes with removing the edges out of an observed set `X`. -/
theorem latentProjection_deleteOutgoing (D : Digraph V) {L X : Set V} (hXL : Disjoint X L) :
    (latentProjection D L).deleteOutgoing X = latentProjection (D.deleteOutgoing X) L := by
  rw [latentProjection, latentProjection, ADMG.project_deleteOutgoing _ hXL,
    ADMG.deleteOutgoing_ofDigraph]

/-! ### Decidability -/

section Decidable

variable [Fintype V] [DecidableEq V]

instance decidableRelLatentStepDigraph (D : Digraph V) (L : Set V) [DecidableRel D.Adj]
    [DecidablePred (· ∈ L)] : DecidableRel (latentStepDigraph D L).Adj :=
  fun a b => inferInstanceAs (Decidable (D.Adj a b ∧ b ∈ L))

instance decidableLatentPath (D : Digraph V) (L : Set V) [DecidableRel D.Adj]
    [DecidablePred (· ∈ L)] (a b : V) : Decidable (LatentPath D L a b) :=
  inferInstanceAs (Decidable (∃ w, ReflTransGen (latentStepDigraph D L).Adj a w ∧ D.Adj w b))

instance decidableLatentAnc (D : Digraph V) (L : Set V) [DecidableRel D.Adj]
    [DecidablePred (· ∈ L)] (a b : V) : Decidable (LatentAnc D L a b) :=
  inferInstanceAs (Decidable (a = b ∨ (a ∈ L ∧ LatentPath D L a b)))

namespace ADMG

variable (G : ADMG V) (L : Set V) [DecidablePred (· ∈ L)]

instance decidableRelProjectDirected [DecidableRel G.directed.Adj] :
    DecidableRel (G.project L).directed.Adj :=
  fun u v => inferInstanceAs (Decidable (u ∉ L ∧ v ∉ L ∧ LatentPath G.directed L u v))

instance decidableRelProjectBidirected [DecidableRel G.directed.Adj]
    [DecidableRel G.bidirected.Adj] : DecidableRel (G.project L).bidirected.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ u ∉ L ∧ v ∉ L ∧
    ((∃ l ∈ L, LatentPath G.directed L l u ∧ LatentPath G.directed L l v) ∨
      ∃ a b, G.bidirected.Adj a b ∧ LatentAnc G.directed L a u ∧ LatentAnc G.directed L b v)))

end ADMG

instance decidableRelLatentProjectionDirected (D : Digraph V) (L : Set V) [DecidableRel D.Adj]
    [DecidablePred (· ∈ L)] : DecidableRel (latentProjection D L).directed.Adj :=
  ADMG.decidableRelProjectDirected (ADMG.ofDigraph D) L

instance decidableRelLatentProjectionBidirected (D : Digraph V) (L : Set V)
    [DecidableRel D.Adj] [DecidablePred (· ∈ L)] :
    DecidableRel (latentProjection D L).bidirected.Adj :=
  ADMG.decidableRelProjectBidirected (ADMG.ofDigraph D) L

end Decidable

end CausalInference
