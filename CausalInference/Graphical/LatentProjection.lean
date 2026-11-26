/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.ADMG

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
  two shapes explicitly.

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

## Main results

* `ADMG.IsAcyclic.project`, `latentProjection_isAcyclic`: the projection of an acyclic graph is
  acyclic.
* `ADMG.isAncestor_project_iff`, `isAncestor_latentProjection_iff`: for observed `u` and `v`,
  `u` is an ancestor of `v` in the projection exactly when it is in the original graph.
* `ADMG.project_empty`, `latentProjection_empty`: projecting out nothing gives the graph back;
  for a DAG, the DAG with no bidirected edges.
* `ADMG.project_project`, `latentProjection_project`: projecting out `L1` and then `L2` is
  projecting out `L1 ∪ L2` in one step.

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
  `LatentAnc G.directed L b v`. -/
def project (G : ADMG V) (L : Set V) : ADMG V where
  directed := { Adj := fun u v => u ∉ L ∧ v ∉ L ∧ LatentPath G.directed L u v }
  bidirected :=
    { Adj := G.ProjectBiAdj L
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }

variable {G : ADMG V} {L L1 L2 : Set V} {u v a b : V}

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
