/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.ADMG
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.Setoid.Partition

/-!
# Districts (c-components) of a directed mixed graph

The district of a vertex `v` is the set of vertices reachable from `v` by a path of bidirected
edges, including `v` itself. Equivalently, it is the connected component of `v` in the
bidirected part, a Mathlib `SimpleGraph`, so it is defined through `SimpleGraph.Reachable` and
related to `SimpleGraph.ConnectedComponent`. Districts are the c-components of Tian and Pearl.

## Main definitions

* `ADMG.SameDistrict G u w`: `w` is reachable from `u` by bidirected edges.
* `ADMG.district G v`: the district of `v`.
* `ADMG.districtFinset G v`, `ADMG.districts G`: the finite versions, for a finite vertex type
  with decidable bidirected adjacency, computed by saturation and usable by `decide`.
* `ADMG.districtsOn G S`: the districts of the induced sub-ADMG on a finset `S`, one for each
  vertex of `S`. Since `restrict` keeps the vertex type, `(G.restrict S).districts` also lists a
  singleton for every vertex outside `S`; `districtsOn` lists only the districts inside `S`.

## Main results

* `ADMG.sameDistrict_equivalence`: being in the same district is an equivalence relation.
* `ADMG.isPartition_range_district`: the districts partition `V`; also
  `ADMG.district_eq_or_disjoint`.
* `ADMG.district_eq_connectedComponent`: the district is the support of the connected component.
* `ADMG.district_ofDigraph`: in a DAG every district is a singleton.
* `ADMG.subset_of_mem_districtsOn`, `ADMG.existsUnique_mem_districtsOn`: the members of
  `G.districtsOn S` are nonempty subsets of `S` and every vertex of `S` lies in exactly one of
  them, so they partition `S`.
* `ADMG.district_restrict_subset`: the district of `v` in an induced sub-ADMG is contained in the
  district of `v` in the whole graph. The containment can be strict; an example is in
  `CausalInference.Graphical.ADMGExamples`.

Sources: Tian and Pearl (2002), *A general identification condition for causal effects*;
Richardson (2003), *Markov properties for acyclic directed mixed graphs*.
-/

@[expose] public section

namespace CausalInference

namespace ADMG

open Relation

variable {V : Type*}

/-- `u` and `w` are in the same district: `w` is reachable from `u` by a path of zero or more
bidirected edges. -/
def SameDistrict (G : ADMG V) (u w : V) : Prop := G.bidirected.Reachable u w

/-- The district (c-component) of `v`: all vertices reachable from `v` by bidirected edges,
including `v`. -/
def district (G : ADMG V) (v : V) : Set V := {w | G.SameDistrict v w}

section Sets

variable {G H : ADMG V} {u v w : V} {S : Set V}

@[simp] theorem mem_district : w ∈ G.district v ↔ G.bidirected.Reachable v w := Iff.rfl

theorem sameDistrict_iff_reflTransGen :
    G.SameDistrict u w ↔ ReflTransGen G.bidirected.Adj u w :=
  SimpleGraph.reachable_iff_reflTransGen u w

/-- Being in the same district is an equivalence relation. -/
theorem sameDistrict_equivalence : Equivalence G.SameDistrict :=
  G.bidirected.reachable_is_equivalence

/-- Every vertex is in its own district. -/
theorem mem_district_self (v : V) : v ∈ G.district v := SimpleGraph.Reachable.refl v

/-- District membership is symmetric. -/
theorem mem_district_comm : w ∈ G.district v ↔ v ∈ G.district w :=
  SimpleGraph.reachable_comm

/-- A sibling is in the same district. -/
theorem mem_district_of_adj (h : G.bidirected.Adj v w) : w ∈ G.district v := h.reachable

/-- Two vertices in the same district have the same district. -/
theorem district_eq_of_mem (h : w ∈ G.district v) : G.district w = G.district v := by
  ext x
  exact ⟨fun hx => SimpleGraph.Reachable.trans h hx, fun hx => h.symm.trans hx⟩

theorem district_eq_iff : G.district v = G.district w ↔ w ∈ G.district v :=
  ⟨fun h => h ▸ mem_district_self w, fun h => (district_eq_of_mem h).symm⟩

/-- Two districts are equal or disjoint. -/
theorem district_eq_or_disjoint (v w : V) :
    G.district v = G.district w ∨ Disjoint (G.district v) (G.district w) := by
  by_cases h : w ∈ G.district v
  · exact Or.inl (district_eq_of_mem h).symm
  · refine Or.inr (Set.disjoint_left.2 fun x hxv hxw => h ?_)
    exact SimpleGraph.Reachable.trans hxv hxw.symm

/-- The district of `v` is the support of the connected component of `v` in the bidirected
part. -/
theorem district_eq_connectedComponent (v : V) :
    G.district v = (G.bidirected.connectedComponentMk v).supp := by
  ext w
  simp only [mem_district, SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact ⟨fun h => SimpleGraph.ConnectedComponent.eq.2 h.symm,
    fun h => (SimpleGraph.ConnectedComponent.eq.1 h).symm⟩

/-- The set of districts is the set of equivalence classes of bidirected reachability. -/
theorem range_district : Set.range G.district = G.bidirected.reachableSetoid.classes := by
  ext s
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    ext w
    exact mem_district_comm
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    ext w
    exact mem_district_comm

/-- The districts partition the vertex set: each is nonempty and every vertex lies in exactly
one of them. -/
theorem isPartition_range_district : Setoid.IsPartition (Set.range G.district) :=
  range_district (G := G) ▸ Setoid.isPartition_classes _

/-- With no bidirected edges, every district is a singleton. -/
theorem district_of_bidirected_eq_bot (h : G.bidirected = ⊥) (v : V) : G.district v = {v} := by
  ext w
  rw [mem_district, h, SimpleGraph.reachable_bot, Set.mem_singleton_iff, eq_comm]

/-- In a DAG every district is a singleton. -/
@[simp] theorem district_ofDigraph (D : Digraph V) (v : V) : (ofDigraph D).district v = {v} :=
  district_of_bidirected_eq_bot rfl v

/-- Districts are monotone in the bidirected part. -/
theorem district_mono (h : G.bidirected ≤ H.bidirected) (v : V) : G.district v ⊆ H.district v :=
  fun _ hw => hw.mono h

/-- The district of `v` within the induced sub-ADMG on `S` is contained in the district of `v`
in the whole graph. -/
theorem district_restrict_subset (v : V) : (G.restrict S).district v ⊆ G.district v :=
  district_mono bidirectedRestrict_le v

/-- The district of `v` after `do(X)` is contained in the district of `v` before. -/
theorem district_deleteIncoming_subset (X : Set V) (v : V) :
    (G.deleteIncoming X).district v ⊆ G.district v :=
  district_mono bidirectedRestrict_le v

/-- Within the induced sub-ADMG on `S`, the district of a vertex of `S` stays inside `S`. -/
theorem district_restrict_subset_of_mem (hv : v ∈ S) : (G.restrict S).district v ⊆ S := by
  intro w hw
  rw [mem_district, SimpleGraph.reachable_iff_reflTransGen] at hw
  induction hw with
  | refl => exact hv
  | tail _ hbc _ => exact hbc.2.2

/-- Deleting outgoing directed edges does not change districts. -/
@[simp] theorem district_deleteOutgoing (X : Set V) (v : V) :
    (G.deleteOutgoing X).district v = G.district v := rfl

end Sets

/-! ### Finite vertex types -/

section Finite

/-- The bidirected part seen as a (symmetric) digraph, so that the saturation procedure
`Digraph.reachFinset` of the directed substrate applies to it. -/
def bidirectedDigraph (G : ADMG V) : Digraph V where
  Adj := G.bidirected.Adj

instance decidableRelBidirectedDigraph (G : ADMG V) [DecidableRel G.bidirected.Adj] :
    DecidableRel G.bidirectedDigraph.Adj :=
  inferInstanceAs (DecidableRel G.bidirected.Adj)

variable (G : ADMG V) [Fintype V] [DecidableEq V] [DecidableRel G.bidirected.Adj]

/-- The district of `v` as a finset, computed by saturation along bidirected edges. -/
def districtFinset (v : V) : Finset V := G.bidirectedDigraph.reachFinset v

/-- The finset of all districts. -/
def districts : Finset (Finset V) := Finset.univ.image G.districtFinset

variable {G}

@[simp] theorem mem_districtFinset {v w : V} : w ∈ G.districtFinset v ↔ w ∈ G.district v := by
  rw [districtFinset, Digraph.mem_reachFinset, mem_district,
    SimpleGraph.reachable_iff_reflTransGen]
  rfl

@[simp, norm_cast] theorem coe_districtFinset (v : V) :
    (G.districtFinset v : Set V) = G.district v := by
  ext; simp

instance decidableSameDistrict (u w : V) : Decidable (G.SameDistrict u w) :=
  decidable_of_iff (w ∈ G.districtFinset u) mem_districtFinset

theorem mem_districts {s : Finset V} : s ∈ G.districts ↔ ∃ v, G.districtFinset v = s := by
  simp [districts]

/-- Every vertex lies in exactly one member of `G.districts`. -/
theorem existsUnique_mem_districts (v : V) : ∃! s, s ∈ G.districts ∧ v ∈ s := by
  refine ⟨G.districtFinset v, ⟨mem_districts.2 ⟨v, rfl⟩, by simp⟩,
    ?_⟩
  rintro s ⟨hs, hvs⟩
  obtain ⟨u, rfl⟩ := mem_districts.1 hs
  rw [mem_districtFinset] at hvs
  apply Finset.coe_injective
  rw [coe_districtFinset, coe_districtFinset, district_eq_of_mem hvs]

end Finite

section On

variable (G : ADMG V) [Fintype V] [DecidableEq V] [DecidableRel G.bidirected.Adj]

/-- The districts of the induced sub-ADMG on the finset `S`: the district in `G.restrict S` of
each vertex of `S`. -/
def districtsOn (S : Finset V) : Finset (Finset V) :=
  S.image (G.restrict (S : Set V)).districtFinset

variable {G} {S : Finset V} {d : Finset V} {v : V}

theorem mem_districtsOn :
    d ∈ G.districtsOn S ↔ ∃ v ∈ S, (G.restrict (S : Set V)).districtFinset v = d := by
  simp [districtsOn]

/-- Every member of `G.districtsOn S` is contained in `S`. -/
theorem subset_of_mem_districtsOn (hd : d ∈ G.districtsOn S) : d ⊆ S := by
  obtain ⟨v, hv, rfl⟩ := mem_districtsOn.1 hd
  intro w hw
  rw [mem_districtFinset] at hw
  exact district_restrict_subset_of_mem (S := (S : Set V)) hv hw

/-- Every member of `G.districtsOn S` is nonempty. -/
theorem nonempty_of_mem_districtsOn (hd : d ∈ G.districtsOn S) : d.Nonempty := by
  obtain ⟨v, -, rfl⟩ := mem_districtsOn.1 hd
  exact ⟨v, mem_districtFinset.2 (mem_district_self v)⟩

/-- Every vertex of `S` lies in exactly one member of `G.districtsOn S`. -/
theorem existsUnique_mem_districtsOn (hv : v ∈ S) : ∃! d, d ∈ G.districtsOn S ∧ v ∈ d := by
  refine ⟨(G.restrict (S : Set V)).districtFinset v,
    ⟨mem_districtsOn.2 ⟨v, hv, rfl⟩, mem_districtFinset.2 (mem_district_self v)⟩, ?_⟩
  rintro d ⟨hd, hvd⟩
  obtain ⟨u, -, rfl⟩ := mem_districtsOn.1 hd
  rw [mem_districtFinset] at hvd
  apply Finset.coe_injective
  rw [coe_districtFinset, coe_districtFinset, district_eq_of_mem hvd]

end On

end ADMG

end CausalInference
