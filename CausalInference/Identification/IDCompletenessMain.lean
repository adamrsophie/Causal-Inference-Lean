/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDCompletenessLift

/-!
# Completeness of the identification algorithm under the routing condition

Let `G` be an acyclic directed mixed graph on `V`, with every vertex observed, and `X`, `Y`
disjoint. The **routing condition** (`IDCompleteness.RoutingCondition G X Y`) says: if a
district of the ancestors of `Y` outside `X` has a failure witness, then a routed pair for the
effect of `X` on `Y` exists (`IDCompleteness.RoutedPair`). Under this condition:

* `IDCompleteness.not_identifiableFrom_of_idAlg_eq_none`: if the algorithm fails on the latent
  projection of the canonical DAG, the effect of `X` on `Y` is not identifiable at some
  configuration, within the class of Boolean models on the canonical DAG whose observed law is
  strictly positive;
* `IDCompleteness.identifiableFrom_iff_idAlg`: together with the soundness theorem
  `ADMG.identifiableFrom_of_idAlg_canonical`, the effect is identifiable at every configuration
  if and only if the algorithm succeeds.

The routing condition is a hypothesis of these two results. It is not proved here. It holds
whenever some bidirected connected set inside `Y` has a failure witness that meets `X`
(`IDCompleteness.routingCondition_of_subset`). The form of it with the inner set a district of
the ancestors of `Y` is false in general, which is why a routed pair allows any bidirected
connected inner set.

The bow (`x → y`, `x ↔ y`) and the three vertex graph `W → X → Y`, `W ↔ Y`, `X ↔ W` are
instances, with no hypothesis left (`IDCompleteness.bow_identifiableFrom_iff`,
`IDCompleteness.wit3_not_identifiableFrom`, `IDCompleteness.wit3_identifiableFrom_iff`).
-/

@[expose] public section

namespace CausalInference

open Finset

namespace IDCompleteness

variable {V : Type} [Fintype V] [DecidableEq V] {G : ADMG V} [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj]

/-- A routed pair whose inner set lies inside `Y`: the routing paths are trivial. -/
noncomputable def RoutedPair.ofSubset {X Y C T : Finset V} (hXY : Disjoint X Y) (hCY : C ⊆ Y)
    (hC : BiConnected G C) (hf : IsIdFailure G C T) (hTX : (T ∩ X).Nonempty) :
    RoutedPair G X Y where
  C := C
  T := T
  sub c hc := subset_ancIn (fun v hv => mem_sdiff.2 ⟨mem_univ v, disjoint_right.1 hXY hv⟩)
    (hCY hc)
  conn := hC
  fail := hf
  meets := hTX
  route c hc := by
    have hR : c ∉ T \ C := fun h => (mem_sdiff.1 h).2 hc
    exact mem_routeSet.2 ⟨mem_sdiff.2
      ⟨subset_ancIn (fun v hv => mem_sdiff.2 ⟨mem_univ v, disjoint_right.1 hXY hv⟩) (hCY hc), hR⟩,
      c, mem_sdiff.2 ⟨hCY hc, hR⟩, .refl⟩

/-- **The routing condition** for the effect of `X` on `Y`: if a district of the ancestors of
`Y` outside `X` has a failure witness (so the algorithm fails, `idAlg_eq_none_iff`), then a
routed pair exists. This is carried as a hypothesis by the completeness results of this file;
it is not proved in general. -/
def RoutingCondition (G : ADMG V) [DecidableRel G.directed.Adj] [DecidableRel G.bidirected.Adj]
    (X Y : Finset V) : Prop :=
  (∃ d ∈ G.districtsOn (ancIn G (univ \ X) Y), ∃ T ⊆ univ, IsIdFailure G d T) →
    Nonempty (RoutedPair G X Y)

/-- The routing condition holds when some bidirected connected set inside `Y` has a failure
witness that meets `X`. -/
theorem routingCondition_of_subset {X Y C T : Finset V} (hXY : Disjoint X Y) (hCY : C ⊆ Y)
    (hC : BiConnected G C) (hf : IsIdFailure G C T) (hTX : (T ∩ X).Nonempty) :
    RoutingCondition G X Y :=
  fun _ => ⟨RoutedPair.ofSubset hXY hCY hC hf hTX⟩

/-- **Completeness of the identification algorithm under the routing condition.** Let `G` be
acyclic, `X` and `Y` disjoint, and assume the routing condition. If the algorithm fails on the
latent projection of the canonical DAG, then for some configuration `w` the effect
`P(Y = w_Y | do(X := w_X))` is not identifiable from the observed law within the class of
Boolean models on the canonical DAG whose observed law is strictly positive. -/
theorem not_identifiableFrom_of_idAlg_eq_none (hG : G.IsAcyclic) (ord' : V ⊕ V × V → ℕ)
    {X Y : Finset V} (hXY : Disjoint X Y) (hroute : RoutingCondition G X Y)
    (hnone : idAlg (G.embed Function.Embedding.inl) ord' ADMG.canonicalObs
      (X.map .inl) (Y.map .inl) = none) :
    ∃ w, ¬ SCM.IdentifiableFrom
      {m : SCM.Model G.canonicalDAG (fun _ => Bool) |
        ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
      (fun m => m.scm.effect (X.map .inl) w (Y.map .inl) w) := by
  have h := (ADMG.idAlg_canonical_eq_none_iff G ord' (fun _ => 0) univ X Y).1 hnone
  rw [idAlg_eq_none_iff _ ⟨subset_univ _,
    fun y hy => mem_sdiff.2 ⟨mem_univ _, disjoint_right.1 hXY hy⟩⟩] at h
  obtain ⟨P⟩ := hroute h
  obtain ⟨w, -, hw⟩ := not_identifiableFrom_effect hG hXY P fun _ => true
  exact ⟨w, hw⟩

/-- **The algorithm decides identifiability under the routing condition.** For an acyclic `G`,
disjoint `X` and `Y` satisfying the routing condition, and a topological order `ord'` of the
latent projection of the canonical DAG that is injective on the observed vertices, the effect
of `X` on `Y` is identifiable at every configuration, within the class of Boolean models with a
strictly positive observed law, if and only if the algorithm succeeds. -/
theorem identifiableFrom_iff_idAlg (hG : G.IsAcyclic) (ord' : V ⊕ V × V → ℕ)
    (hinj : Set.InjOn ord' ↑(ADMG.canonicalObs (V := V)))
    (hord : ∀ u v, (G.embed Function.Embedding.inl).directed.Adj u v → ord' u < ord' v)
    {X Y : Finset V} (hXY : Disjoint X Y) (hroute : RoutingCondition G X Y) :
    (∀ w, SCM.IdentifiableFrom
      {m : SCM.Model G.canonicalDAG (fun _ => Bool) |
        ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
      (fun m => m.scm.effect (X.map .inl) w (Y.map .inl) w)) ↔
      (idAlg (G.embed Function.Embedding.inl) ord' ADMG.canonicalObs
        (X.map .inl) (Y.map .inl)).isSome := by
  constructor
  · intro h
    rcases hs : idAlg (G.embed Function.Embedding.inl) ord' ADMG.canonicalObs
      (X.map .inl) (Y.map .inl) with _ | e
    · obtain ⟨w, hw⟩ := not_identifiableFrom_of_idAlg_eq_none hG ord' hXY hroute hs
      exact absurd (h w) hw
    · rfl
  · intro h w
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 h
    exact ADMG.identifiableFrom_of_idAlg_canonical G ord' hinj hord he w

/-! ### Instances -/

section Bow

variable {x y : V}

omit [DecidableRel G.bidirected.Adj] in
/-- The ancestral condition of the bow: `x` is an ancestor of `y` inside `{x, y}`. -/
theorem bow_ancIn (hxy : G.directed.Adj x y) : ancIn G {x, y} {y} = {x, y} := by
  refine Subset.antisymm (ancIn_subset _ _) fun v hv => ?_
  have hy : y ∈ ancIn G {x, y} {y} := subset_ancIn (by simp) (mem_singleton_self y)
  rcases mem_insert.1 hv with rfl | hv
  · exact ancIn_closed (mem_insert_self _ _) hy hxy
  · rw [mem_singleton.1 hv]
    exact hy

omit [Fintype V] [DecidableRel G.directed.Adj] [DecidableRel G.bidirected.Adj] in
/-- The failure witness `{x, y}` of a bow is bidirected connected. -/
theorem bow_biConnected (hb : G.bidirected.Adj x y) : BiConnected G {x, y} := by
  have hr : (G.restrict ↑({x, y} : Finset V)).bidirected.Reachable x y :=
    SimpleGraph.Adj.reachable ⟨hb, by simp, by simp⟩
  have key : ∀ u ∈ ({x, y} : Finset V),
      (G.restrict ↑({x, y} : Finset V)).bidirected.Reachable u y := by
    intro u hu
    rcases mem_insert.1 hu with h | h
    · rw [h]; exact hr
    · rw [mem_singleton.1 h]
  exact fun u hu v hv => (key u hu).trans (key v hv).symm

/-- The routed pair of a bow: inner set `{y}`, failure witness `{x, y}`. -/
noncomputable def bowPair (hxy : G.directed.Adj x y) (hb : G.bidirected.Adj x y) :
    RoutedPair G {x} {y} :=
  RoutedPair.ofSubset (disjoint_singleton.2 hb.ne) Subset.rfl
    (fun u hu v hv => by rw [mem_singleton.1 hu, mem_singleton.1 hv])
    ⟨(ssubset_iff_of_subset (by simp)).2 ⟨x, by simp, by simp [hb.ne]⟩, bow_biConnected hb,
      bow_ancIn hxy⟩
    ⟨x, by simp⟩

/-- **The bow from the general theorem.** On the canonical DAG of an acyclic `G` with `x → y`
and `x ↔ y`, the effect of `x` on `y` is identifiable at every configuration, within the class
of Boolean models with a strictly positive observed law, if and only if the algorithm succeeds
on the latent projection. Both sides are false; the left side by
`IDCompleteness.not_identifiableFrom_effect` for the routed pair `bowPair`. -/
theorem bow_identifiableFrom_iff (hG : G.IsAcyclic) (hxy : G.directed.Adj x y)
    (hb : G.bidirected.Adj x y) (ord' : V ⊕ V × V → ℕ) :
    (∀ w, SCM.IdentifiableFrom
      {m : SCM.Model G.canonicalDAG (fun _ => Bool) |
        ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
      (fun m => m.scm.effect {.inl x} w {.inl y} w)) ↔
      (idAlg (G.embed Function.Embedding.inl) ord' ADMG.canonicalObs {.inl x} {.inl y}).isSome
    := by
  rw [IDCompletenessBow.idAlg_canonical_eq_none hxy hb]
  obtain ⟨w, -, hw⟩ := not_identifiableFrom_effect hG (disjoint_singleton.2 hb.ne)
    (bowPair hxy hb) fun _ => true
  rw [map_singleton, map_singleton] at hw
  exact ⟨fun h => absurd (h w) hw, fun h => absurd h (by simp)⟩

end Bow

section Wit3

/-- The three vertex graph on `Fin 3`: `W = 0 → X = 1 → Y = 2`, `W ↔ Y` and `X ↔ W`. -/
def wit3 : ADMG (Fin 3) := IDExamples.mixed [(0, 1), (1, 2)] [(0, 2), (1, 0)]

instance : DecidableRel wit3.directed.Adj :=
  inferInstanceAs (DecidableRel (IDExamples.mixed _ _).directed.Adj)
instance : DecidableRel wit3.bidirected.Adj :=
  inferInstanceAs (DecidableRel (IDExamples.mixed _ _).bidirected.Adj)

/-- The three vertex graph is acyclic. -/
theorem wit3_isAcyclic : wit3.IsAcyclic :=
  Digraph.isAcyclic_of_adj_lt (fun v : Fin 3 => v.val) fun u v h => by
    revert u v h
    decide

/-- Every vertex of the three vertex graph is an ancestor of `Y`. -/
theorem wit3_ancIn : ancIn wit3 univ {2} = univ := by
  refine Subset.antisymm (ancIn_subset _ _) fun v _ => ?_
  have h2 : (2 : Fin 3) ∈ ancIn wit3 univ {2} := subset_ancIn (subset_univ _) (by simp)
  have h1 : (1 : Fin 3) ∈ ancIn wit3 univ {2} := ancIn_closed (mem_univ _) h2 (by decide)
  have h0 : (0 : Fin 3) ∈ ancIn wit3 univ {2} := ancIn_closed (mem_univ _) h1 (by decide)
  fin_cases v
  · exact h0
  · exact h1
  · exact h2

/-- The three vertex graph is bidirected connected. -/
theorem wit3_biConnected : BiConnected wit3 univ := by
  have r02 : (wit3.restrict ↑(univ : Finset (Fin 3))).bidirected.Reachable 0 2 :=
    SimpleGraph.Adj.reachable ⟨by decide, by simp, by simp⟩
  have r12 : (wit3.restrict ↑(univ : Finset (Fin 3))).bidirected.Reachable 1 2 :=
    (SimpleGraph.Adj.reachable ⟨by decide, by simp, by simp⟩ :
      (wit3.restrict ↑(univ : Finset (Fin 3))).bidirected.Reachable 1 0).trans r02
  have key : ∀ u : Fin 3, (wit3.restrict ↑(univ : Finset (Fin 3))).bidirected.Reachable u 2 := by
    intro u
    fin_cases u
    · exact r02
    · exact r12
    · rfl
  exact fun u _ v _ => (key u).trans (key v).symm

/-- The routed pair of the three vertex graph for the effect of `X` on `Y`: inner set `{Y}`,
failure witness all three vertices. -/
noncomputable def wit3Pair : RoutedPair wit3 {1} {2} :=
  RoutedPair.ofSubset (by decide) Subset.rfl
    (fun u hu v hv => by rw [mem_singleton.1 hu, mem_singleton.1 hv])
    ⟨by decide, wit3_biConnected, wit3_ancIn⟩ ⟨1, by decide⟩

/-- **The three vertex graph from the general theorem.** On the canonical DAG of
`W → X → Y`, `W ↔ Y`, `X ↔ W`, with every vertex observed, for every configuration `x` there is
a configuration `w` agreeing with `x` on `X` at which the effect of `X` on `Y` is not
identifiable within the class of Boolean models with a strictly positive observed law. -/
theorem wit3_not_identifiableFrom (x : Fin 3 ⊕ Fin 3 × Fin 3 → Bool) :
    ∃ w : Fin 3 ⊕ Fin 3 × Fin 3 → Bool, (∀ j ∈ ({.inl 1} : Finset _), w j = x j) ∧
      ¬ SCM.IdentifiableFrom
        {m : SCM.Model wit3.canonicalDAG (fun _ => Bool) |
          ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
        (fun m => m.scm.effect {.inl 1} w {.inl 2} w) := by
  have := not_identifiableFrom_effect wit3_isAcyclic (by decide) wit3Pair x
  simpa only [map_singleton, Function.Embedding.inl_apply] using this

/-- **The algorithm decides identifiability on the three vertex graph.** For a topological
order `ord'` of the latent projection of the canonical DAG that is injective on the observed
vertices, the effect of `X` on `Y` is identifiable at every configuration if and only if the
algorithm succeeds. -/
theorem wit3_identifiableFrom_iff (ord' : Fin 3 ⊕ Fin 3 × Fin 3 → ℕ)
    (hinj : Set.InjOn ord' ↑(ADMG.canonicalObs (V := Fin 3)))
    (hord : ∀ u v, (wit3.embed Function.Embedding.inl).directed.Adj u v → ord' u < ord' v) :
    (∀ w, SCM.IdentifiableFrom
      {m : SCM.Model wit3.canonicalDAG (fun _ => Bool) |
        ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
      (fun m => m.scm.effect {.inl 1} w {.inl 2} w)) ↔
      (idAlg (wit3.embed Function.Embedding.inl) ord' ADMG.canonicalObs
        {.inl 1} {.inl 2}).isSome := by
  have := identifiableFrom_iff_idAlg wit3_isAcyclic ord' hinj hord (X := {1}) (Y := {2})
    (by decide) fun _ => ⟨wit3Pair⟩
  simpa only [map_singleton, Function.Embedding.inl_apply] using this

end Wit3

end IDCompleteness

end CausalInference
