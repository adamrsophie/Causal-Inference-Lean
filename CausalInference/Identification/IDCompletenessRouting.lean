/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDCompletenessMain
public import CausalInference.Identification.IDNonIdent

/-!
# General pairs and the routing condition

A **general pair** for the effect of `X` on `Y` (`IDCompleteness.IsGenPair`) is a bidirected
connected set `C` of ancestors of `Y` outside `X` together with a failure witness `T` of `C`
that meets `X`. It is **routed** (`IDCompleteness.Routed`) when every vertex of `C` reaches
`Y \ (T \ C)` by a directed path inside `D \ (T \ C)`, where `D` is the set of ancestors of `Y`
outside `X`; a routed general pair is a routed pair (`IDCompleteness.IsGenPair.toRoutedPair`).

Every failure witness of a district of `D` gives a general pair
(`IDCompleteness.isGenPair_of_district`), and a vertex of `T ∩ D` joined by a bidirected edge to
the inner set can be added to it with the same witness (`IDCompleteness.IsGenPair.insertVertex`).
The routing condition follows once every general pair can be traded for a routed general pair
(`IDCompleteness.routingCondition_of_routed`); that exchange is not proved here.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace IDCompleteness

variable {V : Type} [Fintype V] [DecidableEq V] {G : ADMG V} [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj]

/-- A **general pair** for the effect of `X` on `Y`: a bidirected connected set `C` of ancestors
of `Y` outside `X` and a failure witness `T` of `C` meeting `X`. -/
structure IsGenPair (G : ADMG V) [DecidableRel G.directed.Adj] (X Y C T : Finset V) : Prop where
  /-- The inner set consists of ancestors of `Y` outside `X`. -/
  sub : C ⊆ ancIn G (univ \ X) Y
  /-- The inner set is bidirected connected. -/
  conn : BiConnected G C
  /-- `T` is a failure witness of `C`. -/
  fail : IsIdFailure G C T
  /-- `T` meets `X`. -/
  meets : (T ∩ X).Nonempty

/-- A general pair is **routed** when every vertex of `C` reaches `Y \ (T \ C)` by a directed
path inside `D \ (T \ C)`, with `D` the ancestors of `Y` outside `X`. -/
def Routed (G : ADMG V) [DecidableRel G.directed.Adj] (X Y C T : Finset V) : Prop :=
  ∀ c ∈ C, c ∈ routeSet G (ancIn G (univ \ X) Y) (T \ C) Y

/-- A routed general pair is a routed pair. -/
noncomputable def IsGenPair.toRoutedPair {X Y C T : Finset V} (h : IsGenPair G X Y C T)
    (hr : Routed G X Y C T) : RoutedPair G X Y :=
  ⟨C, T, h.sub, h.conn, h.fail, h.meets, hr⟩

/-- A failure witness of a district of the ancestors of `Y` outside `X` gives a general pair. -/
theorem isGenPair_of_district {X Y d T : Finset V}
    (hd : d ∈ G.districtsOn (ancIn G (univ \ X) Y)) (hf : IsIdFailure G d T) :
    IsGenPair G X Y d T :=
  ⟨ADMG.subset_of_mem_districtsOn hd, biConnected_of_mem_districtsOn hd, hf,
    not_disjoint_iff_nonempty_inter.1 (isIdFailure_not_disjoint hd (subset_univ _) hf).1⟩

omit [DecidableRel G.bidirected.Adj] in
/-- **Enlarging the inner set.** A vertex of `T ∩ D` joined by a bidirected edge to the inner set
of a general pair can be added to it, with the same witness. -/
theorem IsGenPair.insertVertex {X Y C T : Finset V} (h : IsGenPair G X Y C T) {u v : V} (hu : u ∈ C)
    (hvT : v ∈ T) (hvD : v ∈ ancIn G (univ \ X) Y) (huv : G.bidirected.Adj u v) :
    IsGenPair G X Y (insert v C) T := by
  have hsub : insert v C ⊆ ancIn G (univ \ X) Y := insert_subset hvD h.sub
  have hsubT : insert v C ⊆ T := insert_subset hvT h.fail.ssubset.subset
  refine ⟨hsub, ?_, ⟨?_, h.fail.connected, ?_⟩, h.meets⟩
  · have key : ∀ w ∈ insert v C,
        (G.restrict ↑(insert v C)).bidirected.Reachable w u := by
      intro w hw
      rcases mem_insert.1 hw with rfl | hw
      · exact SimpleGraph.Adj.reachable ⟨huv.symm, by simp, by simp [hu]⟩
      · exact reachable_restrict_mono (subset_insert _ _) (h.conn w hw u hu)
    exact fun a ha b hb => (key a ha).trans (key b hb).symm
  · obtain ⟨x, hx⟩ := h.meets
    obtain ⟨hxT, hxX⟩ := mem_inter.1 hx
    exact (ssubset_iff_of_subset hsubT).2
      ⟨x, hxT, fun hx' => RoutedPair.notMem_X_of_mem_D (hsub hx') hxX⟩
  · refine Subset.antisymm (ancIn_subset _ _) ?_
    have h1 : ancIn G T C ⊆ ancIn G T (insert v C) :=
      ancIn_subset_of_subset ((subset_insert _ _).trans (subset_ancIn hsubT))
    rw [h.fail.ancestral] at h1
    exact h1

/-- The routing condition holds as soon as every general pair can be traded for a routed one.
The hypothesis is the open part of the argument; it is not proved here. -/
theorem routingCondition_of_routed {X Y : Finset V}
    (h : ∀ C T, IsGenPair G X Y C T → ∃ C' T', IsGenPair G X Y C' T' ∧ Routed G X Y C' T') :
    RoutingCondition G X Y := by
  rintro ⟨d, hd, T, -, hf⟩
  obtain ⟨C', T', h', hr⟩ := h d T (isGenPair_of_district hd hf)
  exact ⟨h'.toRoutedPair hr⟩

end IDCompleteness

end CausalInference
