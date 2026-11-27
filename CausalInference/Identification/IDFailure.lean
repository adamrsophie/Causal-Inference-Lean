/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDAlgorithm

/-!
# When the identification algorithm fails

A structural reading of the failure of `idAlg`. The recursion `identify H ord C T q` fails
exactly when it reaches a set `T` that is a single district of `H` restricted to `T`, strictly
contains `C`, and equals the ancestral closure of `C` inside `T`. Tian and Pearl (2002) show
that in this situation `Q[C]` is not identifiable from `Q[T]`, and Shpitser and Pearl (2006)
call the related structures hedges; neither non-identifiability result is proved here.

## Main definitions

* `BiConnected H T`: every two vertices of `T` are joined by a path of bidirected edges inside
  `T`, so `T` is a single district of `H` restricted to `T`.
* `IsIdFailure H C T`: `C ⊂ T`, `T` is bidirected-connected, and every vertex of `T` is an
  ancestor of `C` inside `T`.

## Main results

* `identify_eq_none_iff`: for nonempty bidirected-connected `C ⊆ T` with `T`
  bidirected-connected, `identify H ord C T q = none` if and only if some `T' ⊆ T` satisfies
  `IsIdFailure H C T'`.
* `idAlg_eq_none_iff`: when `X ⊆ O` and `Y ⊆ O \ X`, `idAlg H ord O X Y = none` if and only if
  some district `d` of `H` restricted to the ancestors `D` of `Y` inside `O \ X` has a failure
  witness `T ⊆ O`.

The order `ord` plays no role: failure depends only on the graph.
-/

@[expose] public section

namespace CausalInference

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {H : ADMG V}

/-- `T` is a single district of `H` restricted to `T`: every two of its vertices are joined by a
path of bidirected edges inside `T`. -/
def BiConnected (H : ADMG V) (T : Finset V) : Prop :=
  ∀ u ∈ T, ∀ v ∈ T, (H.restrict ↑T).bidirected.Reachable u v

/-- **A failure witness** for `C`: a set `T ⊋ C` that is a single district of `H` restricted to
`T` and in which every vertex is an ancestor of `C` inside `T`. -/
structure IsIdFailure (H : ADMG V) [DecidableRel H.directed.Adj] (C T : Finset V) : Prop where
  /-- `C` is a proper subset of `T`. -/
  ssubset : C ⊂ T
  /-- `T` is a single district of `H` restricted to `T`. -/
  connected : BiConnected H T
  /-- Every vertex of `T` is an ancestor of `C` inside `T`. -/
  ancestral : ancIn H T C = T

omit [Fintype V] [DecidableEq V] in
/-- Bidirected reachability inside `S` implies it inside any `T ⊇ S`. -/
theorem reachable_restrict_mono {S T : Finset V} (h : S ⊆ T) {u v : V}
    (huv : (H.restrict ↑S).bidirected.Reachable u v) :
    (H.restrict ↑T).bidirected.Reachable u v := by
  have hle : (H.restrict ↑S).bidirected ≤ (H.restrict ↑T).bidirected := fun a b hab =>
    ⟨hab.1, coe_subset.2 h hab.2.1, coe_subset.2 h hab.2.2⟩
  exact huv.mono hle

/-- A district of `H` restricted to `A` is a single district of `H` restricted to itself. -/
theorem biConnected_districtFinset [DecidableRel H.bidirected.Adj] (A : Finset V) (c : V) :
    BiConnected H ((H.restrict ↑A).districtFinset c) := by
  set s := (H.restrict ↑A).districtFinset c
  have hmem : ∀ u, Relation.ReflTransGen (H.restrict ↑A).bidirected.Adj c u → u ∈ s :=
    fun u hu => ADMG.mem_districtFinset.2 ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hu)
  have key : ∀ u, Relation.ReflTransGen (H.restrict ↑A).bidirected.Adj c u →
      (H.restrict ↑s).bidirected.Reachable c u := by
    intro u hu
    induction hu with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail hcb hbu ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      exact ⟨hbu.1, mem_coe.2 (hmem _ hcb), mem_coe.2 (hmem _ (hcb.tail hbu))⟩
  have hc : ∀ u ∈ s, (H.restrict ↑s).bidirected.Reachable c u := fun u hu =>
    key u ((SimpleGraph.reachable_iff_reflTransGen _ _).1 (ADMG.mem_districtFinset.1 hu))
  exact fun u hu v hv => (hc u hu).symm.trans (hc v hv)

/-- A member of `H.districtsOn D` is a single district of `H` restricted to itself. -/
theorem biConnected_of_mem_districtsOn [DecidableRel H.bidirected.Adj] {D d : Finset V}
    (hd : d ∈ H.districtsOn D) : BiConnected H d := by
  obtain ⟨v, -, rfl⟩ := ADMG.mem_districtsOn.1 hd
  exact biConnected_districtFinset D v

/-- A bidirected-connected `T ⊆ A` that meets the nonempty `C ⊆ T` lies in the union of the
districts inside `A` meeting `C`. -/
theorem subset_closeIn_of_biConnected [DecidableRel H.bidirected.Adj] {A C T : Finset V}
    (hC : C.Nonempty) (hCT : C ⊆ T) (hTA : T ⊆ A) (hT : BiConnected H T) :
    T ⊆ closeIn H A C := by
  obtain ⟨c, hc⟩ := hC
  intro v hv
  exact mem_inter.2 ⟨mem_biUnion.2 ⟨c, hc, ADMG.mem_districtFinset.2
    (reachable_restrict_mono hTA (hT c (hCT hc) v hv))⟩, hTA hv⟩

/-- If every vertex of `T' ⊆ T` is an ancestor of `C` inside `T'`, then `T'` lies in the
ancestral closure of `C` inside `T`. -/
theorem subset_ancIn_of_ancestral [DecidableRel H.directed.Adj] {C T T' : Finset V}
    (hT'T : T' ⊆ T) (hanc : ancIn H T' C = T') : T' ⊆ ancIn H T C := by
  intro v hv
  rw [← hanc] at hv
  obtain ⟨hv, hvT'⟩ := mem_inter.1 hv
  obtain ⟨s, hs, hp⟩ := ADMG.mem_ancestorsOfFinset.1 hv
  have hmono : ∀ a b, (H.restrict ↑T').directed.Adj a b → (H.restrict ↑T).directed.Adj a b :=
    fun a b hab => ⟨hab.1, coe_subset.2 hT'T hab.2.1, coe_subset.2 hT'T hab.2.2⟩
  have key : ∀ b, Relation.ReflTransGen (H.restrict ↑T').directed.Adj v b →
      Relation.ReflTransGen (H.restrict ↑T).directed.Adj v b := by
    intro b hb
    induction hb with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail (hmono _ _ hbc)
  exact mem_inter.2 ⟨ADMG.mem_ancestorsOfFinset.2 ⟨s, hs, key s hp⟩, hT'T hvT'⟩

/-- The union of the districts inside `A` meeting a nonempty bidirected-connected `C ⊆ A` is a
single district of `H` restricted to itself. -/
theorem biConnected_closeIn [DecidableRel H.bidirected.Adj] {A C : Finset V} (hC : C.Nonempty)
    (hCA : C ⊆ A) (hconn : BiConnected H C) : BiConnected H (closeIn H A C) := by
  obtain ⟨c, hc⟩ := hC
  set D0 := (H.restrict ↑A).districtFinset c
  have h1 : D0 ⊆ closeIn H A C := fun v hv =>
    mem_inter.2 ⟨mem_biUnion.2 ⟨c, hc, hv⟩,
      mem_coe.1 (ADMG.district_restrict_subset_of_mem (mem_coe.2 (hCA hc))
        (ADMG.mem_districtFinset.1 hv))⟩
  have h2 : closeIn H A C ⊆ D0 := by
    intro v hv
    obtain ⟨c', hc', hv'⟩ := mem_biUnion.1 (mem_inter.1 hv).1
    exact ADMG.mem_districtFinset.2
      ((reachable_restrict_mono hCA (hconn c hc c' hc')).trans (ADMG.mem_districtFinset.1 hv'))
  intro u hu v hv
  exact reachable_restrict_mono h1 (biConnected_districtFinset A c u (h2 hu) v (h2 hv))

/-- **Failure of the recursive step**: for nonempty bidirected-connected `C ⊆ T` with `T`
bidirected-connected, `identify H ord C T q` fails if and only if some `T' ⊆ T` is a failure
witness for `C`. -/
theorem identify_eq_none_iff [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]
    (ord : V → ℕ) : ∀ (T C : Finset V) (q : IdExpr V), C.Nonempty → C ⊆ T →
      BiConnected H C → BiConnected H T →
      (identify H ord C T q = none ↔ ∃ T' ⊆ T, IsIdFailure H C T') := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro C q hne hCT hC hT
    rw [identify]
    split_ifs with h₁ h₂
    · simp only [false_iff]
      rintro ⟨T', hT'T, hf⟩
      have h := subset_ancIn_of_ancestral hT'T hf.ancestral
      rw [h₁] at h
      exact not_subset_of_ssubset hf.ssubset h
    · have hCA : C ⊆ ancIn H T C := subset_ancIn hCT
      rw [ih _ ((closeIn_subset _ _).trans_ssubset h₂) C _ hne (subset_closeIn hCA) hC
        (biConnected_closeIn hne hCA hC)]
      constructor
      · rintro ⟨T', h, hf⟩
        exact ⟨T', h.trans ((closeIn_subset _ _).trans (ancIn_subset _ _)), hf⟩
      · rintro ⟨T', h, hf⟩
        exact ⟨T', subset_closeIn_of_biConnected hne hf.ssubset.subset
          (subset_ancIn_of_ancestral h hf.ancestral) hf.connected, hf⟩
    · simp only [true_iff]
      have hA : ancIn H T C = T := by
        by_contra hne'
        exact h₂ (Finset.ssubset_iff_subset_ne.2 ⟨ancIn_subset T C, hne'⟩)
      exact ⟨T, subset_rfl, Finset.ssubset_iff_subset_ne.2 ⟨hCT, fun h => h₁ (hA.trans h.symm)⟩, hT,
        hA⟩

/-- **Failure of a district call**: for a district `d` of `H` restricted to `D ⊆ O`, the call
`idPart H ord O d` fails if and only if `d` has a failure witness `T ⊆ O`. -/
theorem idPart_eq_none_iff [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]
    (ord : V → ℕ) {O D d : Finset V} (hd : d ∈ H.districtsOn D) (hDO : D ⊆ O) :
    idPart H ord O d = none ↔ ∃ T ⊆ O, IsIdFailure H d T := by
  have hne := ADMG.nonempty_of_mem_districtsOn hd
  have hdO : d ⊆ O := (ADMG.subset_of_mem_districtsOn hd).trans hDO
  have hconn := biConnected_of_mem_districtsOn hd
  rw [idPart, identify_eq_none_iff ord _ d _ hne (subset_closeIn hdO) hconn
    (biConnected_closeIn hne hdO hconn)]
  constructor
  · rintro ⟨T, hT, hf⟩
    exact ⟨T, hT.trans (closeIn_subset _ _), hf⟩
  · rintro ⟨T, hT, hf⟩
    exact ⟨T, subset_closeIn_of_biConnected hne hf.ssubset.subset hT hf.connected, hf⟩

/-- **Structural reading of the failure of the identification algorithm.** When `X ⊆ O` and
`Y ⊆ O \ X`, `idAlg H ord O X Y` fails if and only if some district `d` of `H` restricted to
the ancestors `D` of `Y` inside `O \ X` has a failure witness `T ⊆ O`: a set `T ⊋ d` that is a
single district of `H` restricted to `T` and in which every vertex is an ancestor of `d` inside
`T`. -/
theorem idAlg_eq_none_iff [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]
    (ord : V → ℕ) {O X Y : Finset V} (h₁ : X ⊆ O ∧ Y ⊆ O \ X) :
    idAlg H ord O X Y = none ↔
      ∃ d ∈ H.districtsOn (ancIn H (O \ X) Y), ∃ T ⊆ O, IsIdFailure H d T := by
  have hDO : ancIn H (O \ X) Y ⊆ O := (ancIn_subset _ _).trans sdiff_subset
  rw [idAlg, ite_eq_left h₁]
  split_ifs with h₂
  · simp only [false_iff, not_exists, not_and]
    intro d hd T hT hf
    have h := (idPart_eq_none_iff ord hd hDO).2 ⟨T, hT, hf⟩
    have := h₂ d hd
    rw [h] at this
    exact absurd this (by simp)
  · simp only [true_iff]
    push Not at h₂
    obtain ⟨d, hd, hnone⟩ := h₂
    exact ⟨d, hd, (idPart_eq_none_iff ord hd hDO).1 (Option.not_isSome_iff_eq_none.1 hnone)⟩

end CausalInference
