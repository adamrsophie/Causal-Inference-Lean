/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.MSeparation
public import CausalInference.Identification.IDExamples
public import CausalInference.Identification.IDFailure

/-!
# The canonical DAG of a directed mixed graph and the identification algorithm

Every acyclic directed mixed graph `H₀` on `V` is the latent projection of a DAG: its canonical
DAG `ADMG.canonicalDAG H₀` on `V ⊕ V × V`, in which every bidirected edge `a ↔ b` becomes a
latent root `Sum.inr (a, b)` with edges to `Sum.inl a` and `Sum.inl b`. The latent projection
keeps the vertex type, so it is a graph on `V ⊕ V × V`: the copy `ADMG.embed H₀ Embedding.inl`
of `H₀` along `Sum.inl`, with the latent vertices isolated. The identification algorithm gives
the same verdict on `H₀` and on this copy.

## Main definitions

* `ADMG.embed H f`: the copy of `H : ADMG W` along an embedding `f : W ↪ V`.

## Main results

* `ADMG.IsAcyclic.canonicalDAG` (in `CausalInference.Graphical.MSeparation`): the canonical DAG
  of an acyclic directed mixed graph is acyclic.
* `ADMG.latentProjection_canonicalDAG`: the latent projection of the canonical DAG onto the
  vertices `Sum.inl v` is `ADMG.embed H₀ Embedding.inl`.
* `ADMG.ancIn_embed`, `ADMG.mem_districtsOn_embed`, `ADMG.isIdFailure_embed_iff`: the notions
  used by the identification algorithm commute with `ADMG.embed`.
* `ADMG.idAlg_embed_eq_none_iff`: the algorithm fails on the copy exactly when it fails on the
  original graph, for any two orders.
* `ADMG.idAlg_canonical_eq_none_iff`: the same statement for the projection of the canonical
  DAG.
* `ADMG.identifiableFrom_of_idAlg_canonical`: the soundness theorem on the canonical DAG.
-/

@[expose] public section

namespace CausalInference

open Finset Relation

namespace ADMG

variable {W V : Type*}

/-! ### Copies of a graph along an embedding -/

/-- The copy of the directed mixed graph `H` on `W` along an embedding `f : W ↪ V`: the edges of
`H` between images of vertices, and no edge at a vertex outside the range of `f`. -/
def embed (H : ADMG W) (f : W ↪ V) : ADMG V where
  directed := { Adj := fun x y => ∃ a b, f a = x ∧ f b = y ∧ H.directed.Adj a b }
  bidirected :=
    { Adj := fun x y => ∃ a b, f a = x ∧ f b = y ∧ H.bidirected.Adj a b
      symm := ⟨fun _ _ ⟨a, b, ha, hb, h⟩ => ⟨b, a, hb, ha, h.symm⟩⟩
      loopless := ⟨fun _ ⟨_, _, ha, hb, h⟩ => h.ne (f.injective (ha.trans hb.symm))⟩ }

variable {H : ADMG W} {f : W ↪ V}

/-- The directed edges of the copy between images are the edges of the graph. -/
@[simp] theorem embed_directed_adj {a b : W} :
    (H.embed f).directed.Adj (f a) (f b) ↔ H.directed.Adj a b := by
  simp [embed]

/-- The bidirected edges of the copy between images are the edges of the graph. -/
@[simp] theorem embed_bidirected_adj {a b : W} :
    (H.embed f).bidirected.Adj (f a) (f b) ↔ H.bidirected.Adj a b := by
  simp [embed]

instance [Fintype W] [DecidableEq V] [DecidableRel H.directed.Adj] :
    DecidableRel (H.embed f).directed.Adj := fun x y =>
  inferInstanceAs (Decidable (∃ a b, f a = x ∧ f b = y ∧ H.directed.Adj a b))

instance [Fintype W] [DecidableEq V] [DecidableRel H.bidirected.Adj] :
    DecidableRel (H.embed f).bidirected.Adj := fun x y =>
  inferInstanceAs (Decidable (∃ a b, f a = x ∧ f b = y ∧ H.bidirected.Adj a b))

/-- Paths of a relation on `V` whose steps end in the range of `f` and agree with a relation on
`W` along `f`: from `f a` they reach exactly the images of the vertices reached from `a`. -/
theorem reflTransGen_embed_iff {r : W → W → Prop} {r' : V → V → Prop} (f : W ↪ V)
    (h₁ : ∀ x y, r' x y → ∃ b, f b = y) (h₂ : ∀ a b, r' (f a) (f b) ↔ r a b) (a : W) {y : V} :
    ReflTransGen r' (f a) y ↔ ∃ b, f b = y ∧ ReflTransGen r a b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨a, rfl, ReflTransGen.refl⟩
    | tail _ hyz ih =>
      obtain ⟨c, rfl, hc⟩ := ih
      obtain ⟨d, rfl⟩ := h₁ _ _ hyz
      exact ⟨d, rfl, hc.tail ((h₂ c d).1 hyz)⟩
  · rintro ⟨b, rfl, h⟩
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hcd ih => exact ih.tail ((h₂ _ _).2 hcd)

/-- The two-point form of `ADMG.reflTransGen_embed_iff`. -/
theorem reflTransGen_embed_iff' {r : W → W → Prop} {r' : V → V → Prop} (f : W ↪ V)
    (h₁ : ∀ x y, r' x y → ∃ b, f b = y) (h₂ : ∀ a b, r' (f a) (f b) ↔ r a b) (a b : W) :
    ReflTransGen r' (f a) (f b) ↔ ReflTransGen r a b := by
  rw [reflTransGen_embed_iff f h₁ h₂]
  exact ⟨fun ⟨c, hc, h⟩ => f.injective hc ▸ h, fun h => ⟨b, rfl, h⟩⟩

section Restrict

variable (S : Finset W)

/-- Directed edges of the copy restricted to a copied set. -/
theorem restrict_embed_directed_adj (a b : W) :
    ((H.embed f).restrict ↑(S.map f)).directed.Adj (f a) (f b) ↔
      (H.restrict ↑S).directed.Adj a b := by
  simp [ADMG.restrict, Digraph.restrict]

/-- Bidirected edges of the copy restricted to a copied set. -/
theorem restrict_embed_bidirected_adj (a b : W) :
    ((H.embed f).restrict ↑(S.map f)).bidirected.Adj (f a) (f b) ↔
      (H.restrict ↑S).bidirected.Adj a b := by
  simp [ADMG.restrict, bidirectedRestrict]

/-- A directed edge of the restricted copy ends at an image. -/
theorem exists_of_restrict_embed_directed_adj {x y : V}
    (h : ((H.embed f).restrict ↑(S.map f)).directed.Adj x y) : ∃ b, f b = y := by
  obtain ⟨b, -, hb⟩ := mem_map.1 (mem_coe.1 h.2.2)
  exact ⟨b, hb⟩

/-- A bidirected edge of the restricted copy ends at an image. -/
theorem exists_of_restrict_embed_bidirected_adj {x y : V}
    (h : ((H.embed f).restrict ↑(S.map f)).bidirected.Adj x y) : ∃ b, f b = y := by
  obtain ⟨b, -, hb⟩ := mem_map.1 (mem_coe.1 h.2.2)
  exact ⟨b, hb⟩

/-- Bidirected reachability inside a copied set is reachability inside the original set. -/
theorem reachable_restrict_embed_iff (a : W) {y : V} :
    ((H.embed f).restrict ↑(S.map f)).bidirected.Reachable (f a) y ↔
      ∃ b, f b = y ∧ (H.restrict ↑S).bidirected.Reachable a b := by
  simp only [SimpleGraph.reachable_iff_reflTransGen]
  exact reflTransGen_embed_iff f (fun x y h => exists_of_restrict_embed_bidirected_adj S h)
    (restrict_embed_bidirected_adj S) a

end Restrict

/-! ### The notions of the identification algorithm along an embedding -/

section Transport

variable [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
  [DecidableRel H.directed.Adj] [DecidableRel H.bidirected.Adj]

omit [DecidableRel H.bidirected.Adj] in
/-- The ancestral closure inside a copied set is the copy of the ancestral closure. -/
theorem ancIn_embed (T C : Finset W) :
    ancIn (H.embed f) (T.map f) (C.map f) = (ancIn H T C).map f := by
  have key := fun a b => reflTransGen_embed_iff' (r := (H.restrict ↑T).directed.Adj)
    (r' := ((H.embed f).restrict ↑(T.map f)).directed.Adj) f
    (fun x y h => exists_of_restrict_embed_directed_adj (H := H) (f := f) T h)
    (restrict_embed_directed_adj (H := H) (f := f) T) a b
  ext x
  simp only [ancIn, mem_inter, mem_map, ADMG.mem_ancestorsOfFinset]
  constructor
  · rintro ⟨⟨s, ⟨c, hc, rfl⟩, hp⟩, ⟨a, ha, rfl⟩⟩
    exact ⟨a, ⟨⟨c, hc, (key a c).1 hp⟩, ha⟩, rfl⟩
  · rintro ⟨a, ⟨⟨c, hc, hp⟩, ha⟩, rfl⟩
    exact ⟨⟨f c, ⟨c, hc, rfl⟩, (key a c).2 hp⟩, ⟨a, ha, rfl⟩⟩

omit [DecidableRel H.directed.Adj] in
/-- The district of a copied vertex inside a copied set is the copy of the district. -/
theorem districtFinset_restrict_embed (A : Finset W) (c : W) :
    ((H.embed f).restrict ↑(A.map f)).districtFinset (f c) =
      ((H.restrict ↑A).districtFinset c).map f := by
  ext x
  simp only [ADMG.mem_districtFinset, ADMG.district, ADMG.SameDistrict, Set.mem_ofPred_eq,
    mem_map, reachable_restrict_embed_iff]
  exact ⟨fun ⟨b, hb, h⟩ => ⟨b, h, hb⟩, fun ⟨b, h, hb⟩ => ⟨b, hb, h⟩⟩

omit [DecidableRel H.directed.Adj] in
/-- The districts of a copied set are the copies of the districts. -/
theorem mem_districtsOn_embed {D : Finset W} {d' : Finset V} :
    d' ∈ (H.embed f).districtsOn (D.map f) ↔ ∃ d ∈ H.districtsOn D, d.map f = d' := by
  simp only [ADMG.mem_districtsOn, mem_map]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, (districtFinset_restrict_embed D c).symm⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨f c, ⟨c, hc, rfl⟩, districtFinset_restrict_embed D c⟩

omit [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] [DecidableRel H.directed.Adj]
  [DecidableRel H.bidirected.Adj] in
/-- A copied set is bidirected-connected exactly when the original set is. -/
theorem biConnected_embed_iff {T : Finset W} :
    BiConnected (H.embed f) (T.map f) ↔ BiConnected H T := by
  have key : ∀ a b, ((H.embed f).restrict ↑(T.map f)).bidirected.Reachable (f a) (f b) ↔
      (H.restrict ↑T).bidirected.Reachable a b := fun a b => by
    rw [reachable_restrict_embed_iff]
    exact ⟨fun ⟨c, hc, h⟩ => f.injective hc ▸ h, fun h => ⟨b, rfl, h⟩⟩
  simp only [BiConnected, forall_mem_map, key]

omit [DecidableRel H.bidirected.Adj] in
/-- A failure witness of the copy is the copy of a failure witness. -/
theorem isIdFailure_embed_iff {C T : Finset W} :
    IsIdFailure (H.embed f) (C.map f) (T.map f) ↔ IsIdFailure H C T := by
  constructor
  · intro h
    refine ⟨map_ssubset_map.1 h.ssubset, biConnected_embed_iff.1 h.connected, ?_⟩
    rw [← map_inj (f := f), ← ancIn_embed]
    exact h.ancestral
  · intro h
    refine ⟨map_ssubset_map.2 h.ssubset, biConnected_embed_iff.2 h.connected, ?_⟩
    rw [ancIn_embed, h.ancestral]

/-- **The identification algorithm along an embedding.** For any orders `ord'` on `V` and
`ord` on `W`, the algorithm fails on the copy of `H` along `f`, with the copied sets, exactly
when it fails on `H`. -/
theorem idAlg_embed_eq_none_iff (ord' : V → ℕ) (ord : W → ℕ) (O X Y : Finset W) :
    idAlg (H.embed f) ord' (O.map f) (X.map f) (Y.map f) = none ↔ idAlg H ord O X Y = none := by
  by_cases h : X ⊆ O ∧ Y ⊆ O \ X
  · have h' : X.map f ⊆ O.map f ∧ Y.map f ⊆ O.map f \ X.map f := by
      rw [← map_sdiff]
      exact ⟨map_subset_map.2 h.1, map_subset_map.2 h.2⟩
    rw [idAlg_eq_none_iff ord' h', idAlg_eq_none_iff ord h, ← map_sdiff, ancIn_embed]
    constructor
    · rintro ⟨d', hd', T', hT'O, hf⟩
      obtain ⟨d, hd, rfl⟩ := mem_districtsOn_embed.1 hd'
      obtain ⟨T, hTO, rfl⟩ := subset_map_iff.1 hT'O
      exact ⟨d, hd, T, hTO, isIdFailure_embed_iff.1 hf⟩
    · rintro ⟨d, hd, T, hTO, hf⟩
      exact ⟨d.map f, mem_districtsOn_embed.2 ⟨d, hd, rfl⟩, T.map f, map_subset_map.2 hTO,
        isIdFailure_embed_iff.2 hf⟩
  · have h' : ¬ (X.map f ⊆ O.map f ∧ Y.map f ⊆ O.map f \ X.map f) := by
      rwa [← map_sdiff, map_subset_map, map_subset_map]
    simp only [idAlg, h, h', ↓reduceIte]

end Transport

/-! ### The canonical DAG -/

section Canonical

variable [Fintype V] (G : ADMG V)

instance [DecidableEq V] [DecidableRel G.directed.Adj] [DecidableRel G.bidirected.Adj] :
    DecidableRel G.canonicalDAG.Adj
  | .inl _, .inl _ => decidable_of_iff _ canonicalDAG_adj_inl_inl.symm
  | .inr _, .inl _ => decidable_of_iff _ canonicalDAG_adj_inr_inl.symm
  | _, .inr _ => isFalse not_canonicalDAG_adj_inr

/-- The observed vertices `Sum.inl v` of the canonical DAG. -/
abbrev canonicalObs : Finset (V ⊕ V × V) := (univ : Finset V).map Function.Embedding.inl

/-- The latent vertices of the canonical DAG are roots. -/
theorem canonicalDAG_roots :
    ∀ l ∉ canonicalObs (V := V), ∀ s, ¬ G.canonicalDAG.Adj s l := by
  rintro (v | p) hl s
  · exact absurd (mem_map_of_mem _ (mem_univ v)) hl
  · exact not_canonicalDAG_adj_inr

/-- **The canonical DAG projects onto the graph.** The latent projection of the canonical DAG of
`G` onto the vertices `Sum.inl v` is the copy of `G` along `Sum.inl`. -/
theorem latentProjection_canonicalDAG :
    latentProjection G.canonicalDAG (↑(canonicalObs (V := V)))ᶜ =
      G.embed Function.Embedding.inl := by
  have hroot := canonicalDAG_roots G
  ext s t
  · rw [latentProjection_directed_adj_of_roots hroot]
    rcases s with u | p <;> rcases t with v | q <;> simp [embed]
  · rw [latentProjection_bidirected_adj_of_roots hroot]
    rcases s with u | p <;> rcases t with v | q
    · refine Iff.trans ?_
        (embed_bidirected_adj (H := G) (f := Function.Embedding.inl) (a := u) (b := v)).symm
      constructor
      · rintro ⟨huv, -, -, l, hl, hlu, hlv⟩
        rcases l with w | p
        · exact absurd (mem_map_of_mem _ (mem_univ w)) hl
        · rw [canonicalDAG_adj_inr_inl] at hlu hlv
          obtain ⟨hp, rfl | rfl⟩ := hlu <;> obtain ⟨-, h | h⟩ := hlv
          · exact absurd (congrArg Sum.inl h.symm) huv
          · exact h ▸ hp
          · exact h ▸ hp.symm
          · exact absurd (congrArg Sum.inl h.symm) huv
      · intro h
        refine ⟨fun e => h.ne (Sum.inl_injective e), by simp, by simp, .inr (u, v), by simp,
          ?_, ?_⟩
        · exact canonicalDAG_adj_inr_inl.2 ⟨h, .inl rfl⟩
        · exact canonicalDAG_adj_inr_inl.2 ⟨h, .inr rfl⟩
    all_goals simp [embed]

/-- **The algorithm on the canonical DAG.** For an acyclic `G`, the copy `G.embed inl` is the
latent projection of the acyclic canonical DAG (`ADMG.latentProjection_canonicalDAG`,
`ADMG.IsAcyclic.canonicalDAG`), and the algorithm fails on it, with the copied observed set and
the copied `X` and `Y`, exactly when it fails on `G`. -/
theorem idAlg_canonical_eq_none_iff [DecidableEq V] [DecidableRel G.directed.Adj]
    [DecidableRel G.bidirected.Adj] (ord' : V ⊕ V × V → ℕ) (ord : V → ℕ) (O X Y : Finset V) :
    idAlg (G.embed Function.Embedding.inl) ord' (O.map .inl) (X.map .inl) (Y.map .inl) =
        none ↔ idAlg G ord O X Y = none :=
  idAlg_embed_eq_none_iff ord' ord O X Y

/-- **Soundness on the canonical DAG.** For a topological order `ord'` of the copy
`G.embed inl` that is injective on the observed vertices, if the algorithm succeeds on the
copy, then for every configuration `w` the effect `P(Y = w_Y | do(X := w_X))` is identifiable
from the observed law within the class of models on the canonical DAG whose observed law is
strictly positive. This is `SCM.identifiableFrom_of_idAlg` with
`ADMG.latentProjection_canonicalDAG`. -/
theorem identifiableFrom_of_idAlg_canonical [DecidableEq V] [DecidableRel G.directed.Adj]
    [DecidableRel G.bidirected.Adj] {α : V ⊕ V × V → Type*} [∀ v, Fintype (α v)]
    [∀ v, DecidableEq (α v)] (ord' : V ⊕ V × V → ℕ)
    (hinj : Set.InjOn ord' ↑(canonicalObs (V := V)))
    (hord : ∀ u v, (G.embed Function.Embedding.inl).directed.Adj u v → ord' u < ord' v)
    {X Y : Finset (V ⊕ V × V)} {e : IdExpr (V ⊕ V × V)}
    (he : idAlg (G.embed Function.Embedding.inl) ord' canonicalObs X Y = some e)
    (w : ∀ v, α v) :
    SCM.IdentifiableFrom
      {m : SCM.Model G.canonicalDAG α | ∀ w, 0 < m.scm.dist.margAt canonicalObs w}
      canonicalObs (fun m => m.scm.effect X w Y w) :=
  SCM.identifiableFrom_of_idAlg (latentProjection_canonicalDAG G) ord' hinj hord he w

end Canonical

end ADMG

end CausalInference
