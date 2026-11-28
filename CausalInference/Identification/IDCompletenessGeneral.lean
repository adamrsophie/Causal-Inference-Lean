/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDCompletenessTransport

/-!
# Completeness of the identification algorithm

Let `G` be an acyclic directed mixed graph on `V`, with every vertex observed, and `X`, `Y`
disjoint. This file proves the completeness of the identification algorithm (Shpitser and
Pearl 2006; Huang and Valtorta 2006) with no further hypothesis:

* `IDCompleteness.not_identifiableFrom_effect_of_isGenPair`: for every general pair `(C, T)`
  (`IDCompleteness.IsGenPair`), the effect of `X` on `Y` is not identifiable at some
  configuration agreeing with any given one on `X`;
* `IDCompleteness.not_identifiableFrom_of_idAlg_eq_none_two`: if the algorithm fails on the
  latent projection of the canonical DAG, the effect is not identifiable at some configuration;
* `IDCompleteness.identifiableFrom_iff_idAlg_two` and
  `IDCompleteness.identifiableFrom_iff_idAlg_all`: together with the soundness theorem
  `ADMG.identifiableFrom_of_idAlg_canonical`, the algorithm
  succeeds if and only if the effect is identifiable at every configuration, for the value type
  `Bool × Bool` at every vertex, and equally for every family of finite value types in `Type`.

**Value types.** The countermodels take the value type `Bool × Bool` at every vertex of the
canonical DAG, the latent vertices included (the second bit of a latent vertex is unused), and
the noise type `Bool → Bool` (two independent noise bits) at every vertex. The first bit
carries the hedge construction of `IDCompleteness.Setup.model`; the second bit is the transport
channel of `IDCompleteness.Transport.pscm`. The non-identifiability is within the class of
models on the canonical DAG with these value types whose observed law is strictly positive.

The statement with Boolean values at every vertex is proved in
`CausalInference.Identification.IDCompletenessMain` under the routing condition
(`IDCompleteness.RoutingCondition`), which is not proved in general.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace IDCompleteness

variable {V : Type} [Fintype V] [DecidableEq V] {G : ADMG V} [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj]

/-- **Non-identifiability of the effect from a routed pair into the ancestors of `Y`.** Let `G`
be acyclic, `X` and `Y` disjoint, and `P` a routed pair for the effect of `X` on a set `Z`
lying inside the ancestors of `Y` outside `X`. On the canonical DAG of `G`, with every vertex of
`G` observed and the value type `Bool × Bool` at every vertex, for every configuration `x` there
is a configuration `w` agreeing with `x` on the copy of `X` at which the effect
`P(Y = w_Y | do(X := w_X))` is not identifiable from the observed law within the class of
models whose observed law is strictly positive. The two models are
`IDCompleteness.Transport.pmodel`. -/
theorem not_identifiableFrom_effect_two (hG : G.IsAcyclic) {X Y Z : Finset V}
    (hXY : Disjoint X Y) (P : RoutedPair G X Z) (hZ : Z ⊆ ancIn G (univ \ X) Y)
    (x : V ⊕ V × V → Bool × Bool) :
    ∃ w : V ⊕ V × V → Bool × Bool, (∀ j ∈ X.map .inl, w j = x j) ∧
      ¬ SCM.IdentifiableFrom
        {m : SCM.Model G.canonicalDAG (fun _ => Bool × Bool) |
          ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
        (fun m => m.scm.effect (X.map .inl) w (Y.map .inl) w) := by
  classical
  by_contra hcon
  push Not at hcon
  have hXY' : ∀ j ∈ Y.map .inl, j ∉ (X.map .inl : Finset (V ⊕ V × V)) := by
    intro j hj hj'
    obtain ⟨v, hv, rfl⟩ := mem_map.1 hj
    obtain ⟨u, hu, he⟩ := mem_map.1 hj'
    rw [Function.Embedding.inl_apply, Function.Embedding.inl_apply] at he
    exact disjoint_left.1 hXY (Sum.inl_injective he ▸ hu) hv
  have hmarg : ∀ c : V ⊕ V × V → Bool × Bool,
      ((Transport.pscm P Y hG false).intervene (X.map .inl) x).dist.margAt (Y.map .inl) c =
        ((Transport.pscm P Y hG true).intervene (X.map .inl) x).dist.margAt (Y.map .inl) c := by
    intro c
    let wc : V ⊕ V × V → Bool × Bool := fun j => if j ∈ X.map .inl then x j else c j
    have hwc : ∀ j ∈ X.map .inl, wc j = x j := fun j hj => by simp only [wc, hj, ↓reduceIte]
    have hid := hcon wc hwc (Transport.pmodel P Y hG false)
      (Transport.margAt_pos P Y hG false) (Transport.pmodel P Y hG true)
      (Transport.margAt_pos P Y hG true) (Transport.marginal_eq P Y hG)
    change ((Transport.pscm P Y hG false).intervene (X.map .inl) wc).dist.margAt (Y.map .inl) wc =
      ((Transport.pscm P Y hG true).intervene (X.map .inl) wc).dist.margAt (Y.map .inl) wc at hid
    have hX : ∀ i, ((Transport.pscm P Y hG i).intervene (X.map .inl) wc).dist =
        ((Transport.pscm P Y hG i).intervene (X.map .inl) x).dist := fun i =>
      (Transport.pscm P Y hG i).dist_intervene_congr hwc
    have hY : ∀ i,
        ((Transport.pscm P Y hG i).intervene (X.map .inl) x).dist.margAt (Y.map .inl) wc =
          ((Transport.pscm P Y hG i).intervene (X.map .inl) x).dist.margAt (Y.map .inl) c :=
      fun i => FiniteDist.margAt_congr _ _ fun j hj => by simp only [wc, hXY' j hj, ↓reduceIte]
    rw [hX, hX, hY, hY] at hid
    exact hid
  have hm := marginal_eq_of_margAt_eq hmarg
  have hp := FiniteDist.probOf_eq_of_marginal_eq hm
    (fun τ => Transport.payY P Y τ = true) fun τ τ' h => by
      unfold Transport.payY
      rw [sum_congr rfl fun y hy => by rw [h (.inl y) (mem_map_of_mem _ hy)]]
  rw [SCM.probOf_dist, SCM.probOf_dist, SCM.noiseDist_intervene, SCM.noiseDist_intervene] at hp
  exact Transport.probOf_true_ne P Y hG hXY hZ x true
    (hp ▸ Transport.probOf_false P Y hG hXY hZ x true)

/-- **Non-identifiability of the effect from a general pair**, with no routing hypothesis. Let
`G` be acyclic, `X` and `Y` disjoint, and `(C, T)` a general pair for the effect of `X` on `Y`
(a bidirected connected set `C` of ancestors of `Y` outside `X` with a failure witness `T`
meeting `X`). On the canonical DAG of `G`, with every vertex of `G` observed and the value type
`Bool × Bool` at every vertex, for every configuration `x` there is a configuration `w`
agreeing with `x` on the copy of `X` at which the effect `P(Y = w_Y | do(X := w_X))` is not
identifiable from the observed law within the class of models whose observed law is strictly
positive. -/
theorem not_identifiableFrom_effect_of_isGenPair (hG : G.IsAcyclic) {X Y C T : Finset V}
    (hXY : Disjoint X Y) (h : IsGenPair G X Y C T) (x : V ⊕ V × V → Bool × Bool) :
    ∃ w : V ⊕ V × V → Bool × Bool, (∀ j ∈ X.map .inl, w j = x j) ∧
      ¬ SCM.IdentifiableFrom
        {m : SCM.Model G.canonicalDAG (fun _ => Bool × Bool) |
          ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
        (fun m => m.scm.effect (X.map .inl) w (Y.map .inl) w) :=
  not_identifiableFrom_effect_two hG hXY
    (RoutedPair.ofSubset (disjoint_right.2 fun _ hc => RoutedPair.notMem_X_of_mem_D (h.sub hc))
      Subset.rfl h.conn h.fail h.meets) h.sub x

/-- **Completeness of the identification algorithm.** Let `G` be acyclic and `X`, `Y`
disjoint. If the algorithm fails on the latent projection of the canonical DAG, then for some
configuration `w` the effect `P(Y = w_Y | do(X := w_X))` is not identifiable from the observed
law within the class of models on the canonical DAG with the value type `Bool × Bool` at every
vertex whose observed law is strictly positive. No routing hypothesis is needed; the Boolean
form of this statement is `IDCompleteness.not_identifiableFrom_of_idAlg_eq_none`, under the
routing condition. -/
theorem not_identifiableFrom_of_idAlg_eq_none_two (hG : G.IsAcyclic) (ord' : V ⊕ V × V → ℕ)
    {X Y : Finset V} (hXY : Disjoint X Y)
    (hnone : idAlg (G.embed Function.Embedding.inl) ord' ADMG.canonicalObs
      (X.map .inl) (Y.map .inl) = none) :
    ∃ w, ¬ SCM.IdentifiableFrom
      {m : SCM.Model G.canonicalDAG (fun _ => Bool × Bool) |
        ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
      (fun m => m.scm.effect (X.map .inl) w (Y.map .inl) w) := by
  have h := (ADMG.idAlg_canonical_eq_none_iff G ord' (fun _ => 0) univ X Y).1 hnone
  rw [idAlg_eq_none_iff _ ⟨subset_univ _,
    fun y hy => mem_sdiff.2 ⟨mem_univ _, disjoint_right.1 hXY hy⟩⟩] at h
  obtain ⟨d, hd, T, -, hf⟩ := h
  obtain ⟨w, -, hw⟩ := not_identifiableFrom_effect_of_isGenPair hG hXY
    (isGenPair_of_district hd hf) fun _ => (true, true)
  exact ⟨w, hw⟩

/-- **The algorithm decides identifiability, with two bits per vertex.** For an acyclic `G`,
disjoint `X` and `Y`, and a topological order `ord'` of the latent projection of the canonical
DAG that is injective on the observed vertices, the effect of `X` on `Y` is identifiable at
every configuration, within the class of models with the value type `Bool × Bool` at every
vertex and a strictly positive observed law, if and only if the algorithm succeeds. -/
theorem identifiableFrom_iff_idAlg_two (hG : G.IsAcyclic) (ord' : V ⊕ V × V → ℕ)
    (hinj : Set.InjOn ord' ↑(ADMG.canonicalObs (V := V)))
    (hord : ∀ u v, (G.embed Function.Embedding.inl).directed.Adj u v → ord' u < ord' v)
    {X Y : Finset V} (hXY : Disjoint X Y) :
    (∀ w, SCM.IdentifiableFrom
      {m : SCM.Model G.canonicalDAG (fun _ => Bool × Bool) |
        ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
      (fun m => m.scm.effect (X.map .inl) w (Y.map .inl) w)) ↔
      (idAlg (G.embed Function.Embedding.inl) ord' ADMG.canonicalObs
        (X.map .inl) (Y.map .inl)).isSome := by
  constructor
  · intro h
    rcases hs : idAlg (G.embed Function.Embedding.inl) ord' ADMG.canonicalObs
      (X.map .inl) (Y.map .inl) with _ | e
    · obtain ⟨w, hw⟩ := not_identifiableFrom_of_idAlg_eq_none_two hG ord' hXY hs
      exact absurd (h w) hw
    · rfl
  · intro h w
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 h
    exact ADMG.identifiableFrom_of_idAlg_canonical G ord' hinj hord he w

/-- **The algorithm decides identifiability** (Shpitser and Pearl 2006; Huang and Valtorta
2006). For an acyclic `G`, disjoint `X` and `Y`, and a topological order `ord'` of the latent
projection of the canonical DAG that is injective on the observed vertices, the algorithm
succeeds if and only if, for every family `α` of finite value types in `Type` with decidable
equality and every configuration `w`, the effect `P(Y = w_Y | do(X := w_X))` is identifiable
from the observed law within the class of models on the canonical DAG with value types `α`
whose observed law is strictly positive. Soundness holds for every family; for the converse
the family `Bool × Bool` at every vertex already fails when the algorithm fails. -/
theorem identifiableFrom_iff_idAlg_all (hG : G.IsAcyclic) (ord' : V ⊕ V × V → ℕ)
    (hinj : Set.InjOn ord' ↑(ADMG.canonicalObs (V := V)))
    (hord : ∀ u v, (G.embed Function.Embedding.inl).directed.Adj u v → ord' u < ord' v)
    {X Y : Finset V} (hXY : Disjoint X Y) :
    (∀ (α : V ⊕ V × V → Type) [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] (w : ∀ v, α v),
      SCM.IdentifiableFrom
        {m : SCM.Model G.canonicalDAG α | ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w}
        ADMG.canonicalObs (fun m => m.scm.effect (X.map .inl) w (Y.map .inl) w)) ↔
      (idAlg (G.embed Function.Embedding.inl) ord' ADMG.canonicalObs
        (X.map .inl) (Y.map .inl)).isSome := by
  constructor
  · intro h
    exact (identifiableFrom_iff_idAlg_two hG ord' hinj hord hXY).1 (h fun _ => Bool × Bool)
  · intro h α _ _ w
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 h
    exact ADMG.identifiableFrom_of_idAlg_canonical G ord' hinj hord he w

end IDCompleteness

end CausalInference
