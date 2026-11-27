/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Adjustment

/-!
# Identifiability across the value types of latent vertices

`SCM.IdentifiableFrom C O Q` compares two models of one type `SCM.Model G α`, so the value types
of all vertices, the latent ones (outside `O`) included, are the same in both models. Pearl's
Definition 3.2.4 compares any two models with graph `G`, whatever the domains of the latent
variables. This file removes the restriction.

## Main definitions

* `SCM.retype M ι`: the model `M` with its value types enlarged along injections
  `ι v : α v → β v`. Its solution is `ι ∘ M.solve`, so it has the same graph and noise, and its
  laws are the images of those of `M`.
* `SCM.MergeType O α α'`: a common value type for two families `α`, `α'`: `α v` on the observed
  vertices `v ∈ O`, and `α v ⊕ α' v` on the latent ones, with the embeddings `SCM.mergeLeft` and
  `SCM.mergeRight` (the latter through equivalences `e v : α v ≃ α' v` on `O`).
* `SCM.ObsAgree O e p p'`: two laws on configurations of different value types have the same
  marginal on `O`, read through `e`.
* `SCM.IdentifiableAcross C C' O e Q Q'`: identifiability across value types: any model of `C`
  (value types `α`) and any model of `C'` (value types `α'`) with the same observed law give
  the same value of the query.

## Main results

* `SCM.identifiableAcross_of_identifiableFrom` (**reduction**): if the query is identifiable in
  the fixed-type sense at the merged value types, both classes are mapped into the merged class
  by re-typing, and the query is invariant under re-typing, then it is identifiable across
  value types.
* `SCM.identifiableAcross_effect_singleton_of_subset` (Pearl 2009, Theorem 3.2.5, one intervened
  vertex), `SCM.identifiableAcross_effect_of_backDoor` (Theorem 3.3.2) and
  `SCM.identifiableAcross_effect_of_frontDoor` (Theorem 3.3.4): the identification results with
  latent vertices hold across arbitrary finite latent value types.
* `SCM.dist_retype_eq_zero`: the obstruction to positivity on latent coordinates. Re-typing
  gives mass zero to every configuration with a value outside the image of `ι`, so a class
  defined by strict positivity of the full joint law is not closed under re-typing at a latent
  vertex. The classes above constrain only observed coordinates, where `MergeType` keeps the
  value type and the embeddings are bijective.
* `SCM.identifiableAcross_of_embed` and `SCM.identifiableAcross_of_retype`: the reduction along
  arbitrary embeddings, and the transport of identifiability across value types along re-typing.
  With them `SCM.identifiableAcross_of_identifiableFrom_ulift` and the corollaries
  `SCM.identifiableAcross_effect_singleton_of_subset_ulift`,
  `SCM.identifiableAcross_effect_of_backDoor_ulift` and
  `SCM.identifiableAcross_effect_of_frontDoor_ulift` hold for value type families in
  independent universes, through `ULift`.
* `SCM.pad`: a model padded with an independent noise coordinate at every vertex, which the
  structural equations ignore. `SCM.effect_pad`, `SCM.margAt_pad` and `SCM.dist_pad_pos`: it
  has the same effects and observed marginals, and a strictly positive joint law when the
  original model has one and the extra noise has full support.
* `SCM.PadType O α α'`: `α v` on `O` and `α v × α' v` off `O`, filled by the padded embeddings
  `SCM.Model.padLeft` and `SCM.Model.padRight`. `SCM.identifiableAcross_of_identifiableFrom_pad`
  is the reduction through padding; `SCM.identifiableAcross_pos_of_identifiableFrom` is its form
  for the classes of models with a strictly positive joint law, with the effect corollaries
  `SCM.identifiableAcross_effect_pos` and `SCM.identifiableAcross_effect_pos_ulift`.

Source: Pearl (2009), *Causality*, 2nd edition, Definitions 3.2.3 and 3.2.4.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]

/-! ### Re-typing a model along injections -/

section Retype

variable {α β : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- A reference configuration of the model: its solution at a fixed noise value. -/
noncomputable def refConfig : ∀ v, α v :=
  M.solve fun v => Classical.choice (M.noise v).nonempty

/-- The model `M` with its value types enlarged along maps `ι v : α v → β v` (injective in all
results below): the structural function of `v` reads the parent values back through a left
inverse of `ι` and applies `ι v` to the result. Graph, noise types and noise laws are those of
`M`. -/
noncomputable def retype (ι : ∀ v, α v → β v) : SCM G β ε where
  acyclic := M.acyclic
  f v z e := ι v (M.f v (fun p => @Function.invFun _ _ ⟨M.refConfig p⟩ (ι p) (z p)) e)
  noise := M.noise

variable {M} {ι : ∀ v, α v → β v} (hι : ∀ v, Function.Injective (ι v))
include hι

omit [DecidableEq V] in
/-- Reading back through the left inverse recovers the value. -/
theorem invFun_retype (p : V) (a : α p) :
    @Function.invFun _ _ ⟨M.refConfig p⟩ (ι p) (ι p a) = a :=
  @Function.leftInverse_invFun _ _ ⟨M.refConfig p⟩ _ (hι p) a

/-- Under `do(X := x')`, the re-typed model has the image of the solution of `do(X := x)`, when
`ι v (x v) = x' v` on `X`. -/
theorem solve_retype_intervene {X : Finset V} {x : ∀ v, α v} {x' : ∀ v, β v}
    (hx : ∀ v ∈ X, ι v (x v) = x' v) (u : ∀ v, ε v) :
    ((M.retype ι).intervene X x').solve u = fun v => ι v ((M.intervene X x).solve u v) := by
  refine (((M.retype ι).intervene X x').eq_solve_of_isSolution
    ((M.retype ι).isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩)).symm
  · rw [M.solve_intervene_of_mem u hv, hx v hv]
  · change _ = ι v (M.f v (fun p => _) (u v))
    rw [M.solve_intervene_of_notMem u hv]
    congr 2
    funext p
    exact (invFun_retype (M := M) hι p _).symm

omit [DecidableEq V] in
/-- The solution of the re-typed model is the image of the solution. -/
theorem solve_retype (u : ∀ v, ε v) : (M.retype ι).solve u = fun v => ι v (M.solve u v) := by
  classical
  have h := solve_retype_intervene (M := M) hι (X := ∅) (x := M.refConfig)
    (x' := fun v => ι v (M.refConfig v)) (fun v hv => absurd hv (notMem_empty v)) u
  rwa [solve_intervene_empty, solve_intervene_empty] at h

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] [∀ v, Fintype (β v)]
  [∀ v, DecidableEq (β v)]

/-- The interventional law of the re-typed model is the image of the interventional law. -/
theorem dist_retype_intervene {X : Finset V} {x : ∀ v, α v} {x' : ∀ v, β v}
    (hx : ∀ v ∈ X, ι v (x v) = x' v) :
    ((M.retype ι).intervene X x').dist = (M.intervene X x).dist.map fun w v => ι v (w v) := by
  rw [dist, dist, FiniteDist.map_map, noiseDist_intervene, noiseDist_intervene]
  congr 1
  funext u
  exact solve_retype_intervene hι hx u

/-- The law of the re-typed model is the image of the law of the model. -/
theorem dist_retype : (M.retype ι).dist = M.dist.map fun w v => ι v (w v) := by
  rw [dist, dist, FiniteDist.map_map]
  congr 1
  funext u
  exact solve_retype hι u

omit [∀ v, Fintype (ε v)] in
/-- Marginal masses of an image law: at a configuration that is the image of `c` on `S`, the
mass on `S` is the mass of `c` on `S`. -/
theorem margAt_map_of_agree (p : FiniteDist (∀ v, α v)) {S : Finset V} {c : ∀ v, α v}
    {c' : ∀ v, β v} (hc : ∀ v ∈ S, ι v (c v) = c' v) :
    (p.map fun w v => ι v (w v)).margAt S c' = p.margAt S c := by
  rw [FiniteDist.margAt_eq_probOf, FiniteDist.probOf_map, FiniteDist.margAt_eq_probOf]
  refine p.probOf_congr fun w => forall₂_congr fun v hv => ?_
  rw [← hc v hv]
  exact (hι v).eq_iff

/-- Marginal masses of the re-typed model under an intervention. -/
theorem margAt_retype_intervene {X : Finset V} {x : ∀ v, α v} {x' : ∀ v, β v}
    (hx : ∀ v ∈ X, ι v (x v) = x' v) {S : Finset V} {c : ∀ v, α v} {c' : ∀ v, β v}
    (hc : ∀ v ∈ S, ι v (c v) = c' v) :
    ((M.retype ι).intervene X x').dist.margAt S c' = (M.intervene X x).dist.margAt S c := by
  rw [dist_retype_intervene hι hx, margAt_map_of_agree hι _ hc]

/-- Marginal masses of the re-typed model. -/
theorem margAt_retype {S : Finset V} {c : ∀ v, α v} {c' : ∀ v, β v}
    (hc : ∀ v ∈ S, ι v (c v) = c' v) : (M.retype ι).dist.margAt S c' = M.dist.margAt S c := by
  rw [dist_retype hι, margAt_map_of_agree hι _ hc]

/-- **Re-typing preserves causal effects**: with `ι v (x v) = x' v` on `X` and
`ι v (y v) = y' v` on `Y`, `P(Y = y' | do(X := x'))` in the re-typed model is
`P(Y = y | do(X := x))` in `M`. -/
theorem effect_retype {X Y : Finset V} {x y : ∀ v, α v} {x' y' : ∀ v, β v}
    (hx : ∀ v ∈ X, ι v (x v) = x' v) (hy : ∀ v ∈ Y, ι v (y v) = y' v) :
    (M.retype ι).effect X x' Y y' = M.effect X x Y y :=
  margAt_retype_intervene hι hx hy

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
/-- **The obstruction to positivity on latent coordinates**: the re-typed model gives mass zero
to every configuration with a value outside the image of `ι`. So if `ι v` is not surjective at
some vertex, the joint law of the re-typed model is not strictly positive, and a class of models
defined by strict positivity of the full joint law is not closed under re-typing. -/
theorem dist_retype_eq_zero {c' : ∀ v, β v} {v : V} (hv : c' v ∉ Set.range (ι v)) :
    (M.retype ι).dist c' = 0 := by
  have h : univ.filter (fun u => (M.retype ι).solve u = c') = ∅ :=
    filter_eq_empty_iff.2 fun u _ hu => hv ⟨M.solve u v, by rw [← hu, solve_retype hι]⟩
  rw [dist_apply, h, FiniteDist.prob_empty]

end Retype

/-! ### Classes of models closed under re-typing -/

section Closure

variable {α β : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] {M : SCM G α ε}
  {ι : ∀ v, α v → β v} (hι : ∀ v, Function.Injective (ι v))
  [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [∀ v, Fintype (ε v)]
  [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)] in
/-- Where `ι` is surjective, every configuration of the larger types is an image. -/
theorem exists_agree_of_surjective {S : Finset V} (hs : ∀ v ∈ S, Function.Surjective (ι v))
    (c₀ : ∀ v, α v) (c' : ∀ v, β v) : ∃ c : ∀ v, α v, ∀ v ∈ S, ι v (c v) = c' v := by
  classical
  refine ⟨fun v => if h : v ∈ S then (hs v h (c' v)).choose else c₀ v, fun v hv => ?_⟩
  simp only [hv, dite_true]
  exact (hs v hv (c' v)).choose_spec

include hι

/-- **The overlap class of the adjustment for direct causes is closed under re-typing**, when
`ι` is surjective on the parents of `i` and `ι i (x i) = x' i`: if every parent configuration of
positive probability gives `x_i` positive probability in `M`, the same holds in the re-typed
model. -/
theorem overlap_retype (i : V) {x : ∀ v, α v} {x' : ∀ v, β v} (hx : ι i (x i) = x' i)
    (hs : ∀ v ∈ G.parentsFinset i, Function.Surjective (ι v))
    (h : ∀ z : (∀ u : G.parentsFinset i, α u),
      0 < M.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) →
      0 < M.dist.probOf (fun w => w i = x i ∧ (G.parentsFinset i).restrict w = z))
    (z' : ∀ u : G.parentsFinset i, β u)
    (hz' : 0 < (M.retype ι).dist.probOf (fun w => (G.parentsFinset i).restrict w = z')) :
    0 < (M.retype ι).dist.probOf (fun w => w i = x' i ∧ (G.parentsFinset i).restrict w = z') := by
  classical
  let z : ∀ u : G.parentsFinset i, α u := fun p => (hs p p.2 (z' p)).choose
  have hz : ∀ p : G.parentsFinset i, ι p (z p) = z' p := fun p => (hs p p.2 (z' p)).choose_spec
  have key : ∀ w : ∀ v, α v, (G.parentsFinset i).restrict (fun v => ι v (w v)) = z' ↔
      (G.parentsFinset i).restrict w = z := fun w => by
    simp only [funext_iff, Finset.restrict, ← hz]
    exact forall_congr' fun p => (hι p).eq_iff
  rw [dist_retype hι, FiniteDist.probOf_map] at hz' ⊢
  rw [M.dist.probOf_congr key] at hz'
  refine (h z hz').trans_le (le_of_eq (M.dist.probOf_congr fun w => ?_))
  exact and_congr (by rw [← hx]; exact (hι i).eq_iff.symm) (key w).symm

/-- **The back-door positivity class is closed under re-typing**, when `ι` is surjective on
`Z` and `ι v (x v) = x' v` on `X`: `P(z) > 0 → P(x, z) > 0` transfers to the re-typed model. -/
theorem backDoorPos_retype {X Z : Finset V} {x : ∀ v, α v} {x' : ∀ v, β v}
    (hx : ∀ v ∈ X, ι v (x v) = x' v) (hs : ∀ v ∈ Z, Function.Surjective (ι v))
    (h : ∀ c : ∀ u, α u, (∀ u ∈ X, c u = x u) → 0 < M.dist.margAt Z c →
      0 < M.dist.margAt (X ∪ Z) c) (c' : ∀ u, β u) (hcX : ∀ u ∈ X, c' u = x' u)
    (hZ : 0 < (M.retype ι).dist.margAt Z c') : 0 < (M.retype ι).dist.margAt (X ∪ Z) c' := by
  classical
  obtain ⟨c, hc⟩ := exists_agree_of_surjective hs x c'
  let d : ∀ v, α v := fun v => if v ∈ Z then c v else x v
  have hd : ∀ v ∈ X ∪ Z, ι v (d v) = c' v := by
    intro v hv
    by_cases hvZ : v ∈ Z
    · simp only [d, hvZ, ite_true]
      exact hc v hvZ
    · have hvX : v ∈ X := by simpa [hvZ] using hv
      simp only [d, hvZ, ite_false]
      rw [hx v hvX, hcX v hvX]
  rw [margAt_retype hι fun v hv => hd v (mem_union_right X hv)] at hZ
  rw [margAt_retype hι hd]
  exact h d (fun v hv => by
    by_cases hvZ : v ∈ Z
    · simp only [d, hvZ, ite_true]
      exact hι v (by rw [hc v hvZ, hcX v hv, hx v hv])
    · simp only [d, hvZ, ite_false]) hZ

/-- **The front-door positivity class is closed under re-typing**, when `ι` is surjective on
`X ∪ Z`: strict positivity of the law of `(X, Z)` transfers to the re-typed model. -/
theorem margAt_pos_retype {S : Finset V} (hs : ∀ v ∈ S, Function.Surjective (ι v))
    (h : ∀ c : ∀ u, α u, 0 < M.dist.margAt S c) (c' : ∀ u, β u) :
    0 < (M.retype ι).dist.margAt S c' := by
  obtain ⟨c, hc⟩ := exists_agree_of_surjective hs M.refConfig c'
  rw [margAt_retype hι hc]
  exact h c

/-- **Strict positivity of the joint law is preserved by re-typing along bijections.** -/
theorem dist_pos_retype (hs : ∀ v, Function.Surjective (ι v)) (h : ∀ w, 0 < M.dist w)
    (c' : ∀ v, β v) : 0 < (M.retype ι).dist c' := by
  have h' := margAt_pos_retype hι (S := univ) (fun v _ => hs v)
    (fun c => by rw [FiniteDist.margAt_univ]; exact h c) c'
  rwa [FiniteDist.margAt_univ] at h'

end Closure

/-! ### Bundled models -/

/-- A bundled model re-typed along `ι`. -/
noncomputable def Model.retype {α β : V → Type*} (m : Model G α) (ι : ∀ v, α v → β v) :
    Model G β :=
  ⟨m.ε, m.scm.retype ι⟩

/-! ### A common value type for two families -/

section Merge

universe u

variable (O : Finset V) {α α' : V → Type u}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The merged value type of `α` and `α'` relative to the observed set `O`: `α v` at an observed
vertex, and `α v ⊕ α' v` at a latent vertex. -/
def MergeType (α α' : V → Type u) (v : V) : Type u :=
  if v ∈ O then α v else α v ⊕ α' v

omit [Fintype V] [DecidableRel G.Adj] in
instance [∀ v, Fintype (α v)] [∀ v, Fintype (α' v)] (v : V) : Fintype (MergeType O α α' v) := by
  unfold MergeType
  split <;> infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
instance [∀ v, DecidableEq (α v)] [∀ v, DecidableEq (α' v)] (v : V) :
    DecidableEq (MergeType O α α' v) := by
  unfold MergeType
  split <;> infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
theorem mergeType_of_mem {v : V} (h : v ∈ O) : MergeType O α α' v = α v := by
  simp [MergeType, h]

omit [Fintype V] [DecidableRel G.Adj] in
theorem mergeType_of_notMem {v : V} (h : v ∉ O) : MergeType O α α' v = (α v ⊕ α' v) := by
  simp [MergeType, h]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The embedding of `α` into the merged type: the identity on `O`, the left summand off `O`. -/
def mergeLeft (v : V) (a : α v) : MergeType O α α' v :=
  if h : v ∈ O then cast (mergeType_of_mem O h).symm a
  else cast (mergeType_of_notMem O h).symm (Sum.inl a)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The embedding of `α'` into the merged type: `(e v)⁻¹` on `O`, the right summand off `O`. -/
def mergeRight (e : ∀ v, v ∈ O → α v ≃ α' v) (v : V) (a : α' v) : MergeType O α α' v :=
  if h : v ∈ O then cast (mergeType_of_mem O h).symm ((e v h).symm a)
  else cast (mergeType_of_notMem O h).symm (Sum.inr a)

variable {O} (e : ∀ v, v ∈ O → α v ≃ α' v)

omit [Fintype V] [DecidableRel G.Adj] in
theorem mergeLeft_injective (v : V) : Function.Injective (mergeLeft O (α := α) (α' := α') v) := by
  intro a b h
  by_cases hv : v ∈ O
  · simpa [mergeLeft, hv] using h
  · simpa [mergeLeft, hv] using h

omit [Fintype V] [DecidableRel G.Adj] in
theorem mergeRight_injective (v : V) : Function.Injective (mergeRight O e v) := by
  intro a b h
  by_cases hv : v ∈ O
  · simpa [mergeRight, hv] using h
  · simpa [mergeRight, hv] using h

omit [Fintype V] [DecidableRel G.Adj] in
theorem mergeLeft_surjective {v : V} (hv : v ∈ O) :
    Function.Surjective (mergeLeft O (α := α) (α' := α') v) := fun b =>
  ⟨cast (mergeType_of_mem O hv) b, by simp [mergeLeft, hv]⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- On an observed vertex the two embeddings agree through `e`. -/
theorem mergeRight_of_agree {v : V} (hv : v ∈ O) {a : α v} {a' : α' v} (h : e v hv a = a') :
    mergeRight O e v a' = mergeLeft O v a := by
  simp [mergeRight, mergeLeft, hv, ← h]

omit [Fintype V] [DecidableRel G.Adj] in
theorem mergeRight_surjective {v : V} (hv : v ∈ O) : Function.Surjective (mergeRight O e v) :=
  fun b => by
    obtain ⟨a, rfl⟩ := mergeLeft_surjective (α' := α') hv b
    exact ⟨e v hv a, mergeRight_of_agree e hv rfl⟩

end Merge

/-! ### Identifiability across value types -/

section Across

universe u u'

variable {α : V → Type u} {α' : V → Type u'} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
  [∀ v, Fintype (α' v)] [∀ v, DecidableEq (α' v)]

omit [DecidableRel G.Adj] in
/-- Two laws on configurations with value types `α` and `α'` **agree on the observed set `O`**,
read through equivalences `e v : α v ≃ α' v` on `O`: at configurations `c`, `c'` that correspond
on `O`, the marginal masses on `O` are equal. -/
def ObsAgree (O : Finset V) (e : ∀ v, v ∈ O → α v ≃ α' v) (p : FiniteDist (∀ v, α v))
    (p' : FiniteDist (∀ v, α' v)) : Prop :=
  ∀ c c', (∀ v (h : v ∈ O), e v h (c v) = c' v) → p.margAt O c = p'.margAt O c'

/-- **Identifiability across value types**: the queries `Q` on models with value types `α` and
`Q'` on models with value types `α'` are identified from the observed vertices `O` within the
classes `C` and `C'` when any model of `C` and any model of `C'` whose laws agree on `O` (read
through `e`) give the same value. The latent vertices may have unrelated value types; only the
observed ones are matched, by `e`. With `α' = α`, `e` the identity and `Q' = Q` it implies
`SCM.IdentifiableFrom C O Q` (`SCM.identifiableFrom_of_identifiableAcross`). -/
def IdentifiableAcross {R : Type*} (C : Set (Model G α)) (C' : Set (Model G α')) (O : Finset V)
    (e : ∀ v, v ∈ O → α v ≃ α' v) (Q : Model G α → R) (Q' : Model G α' → R) : Prop :=
  ∀ m ∈ C, ∀ m' ∈ C', ObsAgree O e m.scm.dist m'.scm.dist → Q m = Q' m'

omit [DecidableRel G.Adj] [∀ v, Fintype (α' v)] [∀ v, DecidableEq (α' v)] in
/-- Two laws with the same marginal masses on `O` everywhere have the same marginal on `O`. -/
theorem marginal_eq_of_margAt_eq {β : V → Type*} [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    {p q : FiniteDist (∀ v, β v)} {O : Finset V} (h : ∀ c, p.margAt O c = q.margAt O c) :
    p.marginal O = q.marginal O := by
  ext a
  obtain ⟨w₀⟩ := p.nonempty
  rw [← FiniteDist.restrict_override O a w₀, FiniteDist.marginal_restrict,
    FiniteDist.marginal_restrict, h]

/-- The fixed-type notion is the special case of the identity equivalences. -/
theorem identifiableFrom_of_identifiableAcross {R : Type*} {C : Set (Model G α)}
    {O : Finset V} {Q : Model G α → R}
    (h : IdentifiableAcross C C O (fun v _ => Equiv.refl (α v)) Q Q) :
    IdentifiableFrom C O Q := by
  intro m hm m' hm' hobs
  simp only at hobs
  refine h m hm m' hm' fun c c' hc => ?_
  rw [← FiniteDist.marginal_restrict, hobs, FiniteDist.marginal_restrict]
  exact m'.scm.dist.margAt_congr O fun v hv => hc v hv

/-- **Reduction to fixed value types along embeddings.** Let `ι v : α v → β v` and
`ι' v : α' v → β v` be injective, with `ι` surjective on the observed set `O` and
`ι' v (e v h a) = ι v a` there. If the query `Qβ` is identifiable from `O` within a class `Cβ`
of models with value types `β`, re-typing along `ι` maps `C` into `Cβ` and along `ι'` maps `C'`
into `Cβ`, and `Q`, `Q'` are the values of `Qβ` at the re-typed models, then `Q` and `Q'` are
identifiable across value types. The families `α`, `α'` and `β` may live in any universes. -/
theorem identifiableAcross_of_embed {β : V → Type*} [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    {R : Type*} {O : Finset V} {e : ∀ v, v ∈ O → α v ≃ α' v} {C : Set (Model G α)}
    {C' : Set (Model G α')} {Q : Model G α → R} {Q' : Model G α' → R} {ι : ∀ v, α v → β v}
    {ι' : ∀ v, α' v → β v} (hι : ∀ v, Function.Injective (ι v))
    (hι' : ∀ v, Function.Injective (ι' v)) (hs : ∀ v ∈ O, Function.Surjective (ι v))
    (hcomm : ∀ v (h : v ∈ O) (a : α v), ι' v (e v h a) = ι v a) {Cβ : Set (Model G β)}
    {Qβ : Model G β → R} (hid : IdentifiableFrom Cβ O Qβ) (hC : ∀ m ∈ C, m.retype ι ∈ Cβ)
    (hC' : ∀ m ∈ C', m.retype ι' ∈ Cβ) (hQ : ∀ m ∈ C, Qβ (m.retype ι) = Q m)
    (hQ' : ∀ m ∈ C', Qβ (m.retype ι') = Q' m) : IdentifiableAcross C C' O e Q Q' := by
  intro m hm m' hm' hobs
  rw [← hQ m hm, ← hQ' m' hm']
  refine hid _ (hC m hm) _ (hC' m' hm') (marginal_eq_of_margAt_eq fun cβ => ?_)
  obtain ⟨c, hc⟩ := exists_agree_of_surjective hs m.scm.refConfig cβ
  classical
  let c' : ∀ v, α' v := fun v => if h : v ∈ O then e v h (c v) else m'.scm.refConfig v
  have hcc' : ∀ v (h : v ∈ O), e v h (c v) = c' v := fun v h => by simp [c', h]
  change (m.scm.retype ι).dist.margAt O cβ = (m'.scm.retype ι').dist.margAt O cβ
  rw [margAt_retype hι hc, margAt_retype hι' (c := c') fun v hv => by
    rw [← hcc' v hv, hcomm v hv, hc v hv]]
  exact hobs c c' hcc'

/-- **Transport of identifiability across value types along re-typing.** Let
`ι v : α v → αl v` and `ι' v : α' v → αl' v` be injective and surjective on `O`, intertwining
the equivalences `e` and `el` on `O`. If `Ql` and `Ql'` are identifiable across the value types
`αl`, `αl'` within classes `Cl`, `Cl'` that contain the re-typed models of `C` and `C'`, and the
queries agree on the re-typed models, then `Q` and `Q'` are identifiable across `α`, `α'`. -/
theorem identifiableAcross_of_retype {αl : V → Type*} {αl' : V → Type*}
    [∀ v, Fintype (αl v)] [∀ v, DecidableEq (αl v)] [∀ v, Fintype (αl' v)]
    [∀ v, DecidableEq (αl' v)] {R : Type*} {O : Finset V} {e : ∀ v, v ∈ O → α v ≃ α' v}
    {el : ∀ v, v ∈ O → αl v ≃ αl' v} {C : Set (Model G α)} {C' : Set (Model G α')}
    {Cl : Set (Model G αl)} {Cl' : Set (Model G αl')} {Q : Model G α → R} {Q' : Model G α' → R}
    {Ql : Model G αl → R} {Ql' : Model G αl' → R} {ι : ∀ v, α v → αl v}
    {ι' : ∀ v, α' v → αl' v} (hι : ∀ v, Function.Injective (ι v))
    (hι' : ∀ v, Function.Injective (ι' v)) (hs : ∀ v ∈ O, Function.Surjective (ι v))
    (hcomm : ∀ v (h : v ∈ O) (a : α v), el v h (ι v a) = ι' v (e v h a))
    (hid : IdentifiableAcross Cl Cl' O el Ql Ql') (hC : ∀ m ∈ C, m.retype ι ∈ Cl)
    (hC' : ∀ m ∈ C', m.retype ι' ∈ Cl') (hQ : ∀ m ∈ C, Ql (m.retype ι) = Q m)
    (hQ' : ∀ m ∈ C', Ql' (m.retype ι') = Q' m) : IdentifiableAcross C C' O e Q Q' := by
  intro m hm m' hm' hobs
  rw [← hQ m hm, ← hQ' m' hm']
  refine hid _ (hC m hm) _ (hC' m' hm') fun cl cl' hcl => ?_
  obtain ⟨c, hc⟩ := exists_agree_of_surjective hs m.scm.refConfig cl
  classical
  let c' : ∀ v, α' v := fun v => if h : v ∈ O then e v h (c v) else m'.scm.refConfig v
  have hcc' : ∀ v (h : v ∈ O), e v h (c v) = c' v := fun v h => by simp [c', h]
  change (m.scm.retype ι).dist.margAt O cl = (m'.scm.retype ι').dist.margAt O cl'
  rw [margAt_retype hι hc, margAt_retype hι' (c := c') fun v hv => by
    rw [← hcc' v hv, ← hcomm v hv, hc v hv, hcl v hv]]
  exact hobs c c' hcc'

/-- A query pair is identifiable across value types as soon as it is under the assumption that
all value types are nonempty: a model exists only when they are. -/
theorem identifiableAcross_of_nonempty {R : Type*} {C : Set (Model G α)} {C' : Set (Model G α')}
    {O : Finset V} {e : ∀ v, v ∈ O → α v ≃ α' v} {Q : Model G α → R} {Q' : Model G α' → R}
    (h : (∀ v, Nonempty (α v)) → (∀ v, Nonempty (α' v)) → IdentifiableAcross C C' O e Q Q') :
    IdentifiableAcross C C' O e Q Q' := fun m hm m' hm' =>
  h (fun v => ⟨m.scm.refConfig v⟩) (fun v => ⟨m'.scm.refConfig v⟩) m hm m' hm'

end Across

section AcrossMerge

universe u

variable {α α' : V → Type u} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
  [∀ v, Fintype (α' v)] [∀ v, DecidableEq (α' v)]

/-- **Reduction to fixed value types.** Let `Cβ` be a class of models with the merged value
types `MergeType O α α'`, and `Qβ` a query on it that is identifiable from `O` in the
fixed-type sense. If re-typing along `mergeLeft` maps `C` into `Cβ` and along `mergeRight e`
maps `C'` into `Cβ`, and the queries `Q`, `Q'` are the values of `Qβ` at the re-typed models,
then `Q` and `Q'` are identifiable across value types. -/
theorem identifiableAcross_of_identifiableFrom {R : Type*} {O : Finset V}
    {e : ∀ v, v ∈ O → α v ≃ α' v} {C : Set (Model G α)} {C' : Set (Model G α')}
    {Cβ : Set (Model G (MergeType O α α'))} {Q : Model G α → R} {Q' : Model G α' → R}
    {Qβ : Model G (MergeType O α α') → R} (hid : IdentifiableFrom Cβ O Qβ)
    (hC : ∀ m ∈ C, m.retype (mergeLeft O) ∈ Cβ) (hC' : ∀ m ∈ C', m.retype (mergeRight O e) ∈ Cβ)
    (hQ : ∀ m ∈ C, Qβ (m.retype (mergeLeft O)) = Q m)
    (hQ' : ∀ m ∈ C', Qβ (m.retype (mergeRight O e)) = Q' m) :
    IdentifiableAcross C C' O e Q Q' := by
  intro m hm m' hm' hobs
  rw [← hQ m hm, ← hQ' m' hm']
  refine hid _ (hC m hm) _ (hC' m' hm') (marginal_eq_of_margAt_eq fun cβ => ?_)
  obtain ⟨c, hc⟩ := exists_agree_of_surjective (fun v hv => mergeLeft_surjective (α' := α') hv)
    m.scm.refConfig cβ
  classical
  let c' : ∀ v, α' v := fun v => if h : v ∈ O then e v h (c v) else m'.scm.refConfig v
  have hcc' : ∀ v (h : v ∈ O), e v h (c v) = c' v := fun v h => by simp [c', h]
  change (m.scm.retype _).dist.margAt O cβ = (m'.scm.retype _).dist.margAt O cβ
  rw [margAt_retype (mergeLeft_injective (α' := α')) hc,
    margAt_retype (mergeRight_injective e) (c := c') fun v hv => by
      rw [mergeRight_of_agree e hv (hcc' v hv), hc v hv]]
  exact hobs c c' hcc'

end AcrossMerge

/-! ### Identification results across latent value types -/

section Applications

universe u

variable {α α' : V → Type u} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
  [∀ v, Fintype (α' v)] [∀ v, DecidableEq (α' v)] {O : Finset V}
  (e : ∀ v, v ∈ O → α v ≃ α' v)

/-- **Adjustment for direct causes across latent value types** (Pearl 2009, Theorem 3.2.5, one
intervened vertex): let `O ⊇ {i} ∪ PA_i ∪ Y` be observed, and let the treatment values `x i`,
`x' i` and the outcome values `y`, `y'` correspond through `e`. A model with value types `α` and a
model with value types `α'` (the latent vertices having arbitrary, unrelated finite value
types), both with overlap on the supported parent rows and with the same observed law, have the
same effect `P(Y = y | do(X_i = x_i))`. -/
theorem identifiableAcross_effect_singleton_of_subset (i : V) {x : ∀ v, α v} {x' : ∀ v, α' v}
    {Y : Finset V} {y : ∀ v, α v} {y' : ∀ v, α' v}
    (hO : insert i (G.parentsFinset i) ∪ Y ⊆ O) (hx : ∀ h : i ∈ O, e i h (x i) = x' i)
    (hy : ∀ v ∈ Y, ∀ h : v ∈ O, e v h (y v) = y' v) :
    IdentifiableAcross
      {m : Model G α | ∀ z : (∀ u : G.parentsFinset i, α u),
        0 < m.scm.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) →
        0 < m.scm.dist.probOf (fun w => w i = x i ∧ (G.parentsFinset i).restrict w = z)}
      {m : Model G α' | ∀ z : (∀ u : G.parentsFinset i, α' u),
        0 < m.scm.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) →
        0 < m.scm.dist.probOf (fun w => w i = x' i ∧ (G.parentsFinset i).restrict w = z)}
      O e (fun m => m.scm.effect {i} x Y y) (fun m => m.scm.effect {i} x' Y y') := by
  have hiO : i ∈ O := hO (mem_union_left _ (mem_insert_self _ _))
  have hpaO : ∀ v ∈ G.parentsFinset i, v ∈ O := fun v hv =>
    hO (mem_union_left _ (mem_insert_of_mem hv))
  have hYO : ∀ v ∈ Y, v ∈ O := fun v hv => hO (mem_union_right _ hv)
  have hxr : mergeRight O e i (x' i) = mergeLeft O i (x i) :=
    mergeRight_of_agree e hiO (hx hiO)
  refine identifiableAcross_of_identifiableFrom
    (identifiableFrom_effect_singleton_of_subset i (fun v => mergeLeft O v (x v)) Y
      (fun v => mergeLeft O v (y v)) hO) ?_ ?_ ?_ ?_
  · intro m hm z' hz'
    exact overlap_retype (M := m.scm) (mergeLeft_injective (α' := α')) i (x := x)
      (x' := fun v => mergeLeft O v (x v)) rfl
      (fun v hv => mergeLeft_surjective (hpaO v hv)) hm z' hz'
  · intro m hm z' hz'
    exact overlap_retype (M := m.scm) (mergeRight_injective e) i (x := x')
      (x' := fun v => mergeLeft O v (x v)) hxr
      (fun v hv => mergeRight_surjective e (hpaO v hv)) hm z' hz'
  · exact fun m _ => effect_retype (mergeLeft_injective (α' := α')) (fun _ _ => rfl)
      fun _ _ => rfl
  · refine fun m _ => effect_retype (mergeRight_injective e) (fun v hv => ?_) fun v hv => ?_
    · rw [mem_singleton.1 hv]
      exact hxr
    · exact mergeRight_of_agree e (hYO v hv) (hy v hv (hYO v hv))

/-- **Back-door adjustment across latent value types** (Pearl 2009, Theorem 3.3.2): if `Z`
satisfies the back-door criterion relative to `(X, Y)`, `Y` is disjoint from `Z`, the observed
set contains `X ∪ Y ∪ Z`, and the values `v`, `v'` correspond through `e` on `X ∪ Y`, then a model
with value types `α` and a model with value types `α'`, both satisfying the back-door positivity
and with the same observed law, have the same effect `P(y | do(x))`, whatever the value types of
the latent vertices. -/
theorem identifiableAcross_effect_of_backDoor {X Y Z : Finset V} (v : ∀ u, α u)
    (v' : ∀ u, α' u) (hbd : G.BackDoor ↑X ↑Y ↑Z) (hYZ : Disjoint Y Z) (hO : X ∪ Y ∪ Z ⊆ O)
    (hv : ∀ u ∈ X ∪ Y, ∀ h : u ∈ O, e u h (v u) = v' u) :
    IdentifiableAcross
      {m : Model G α | ∀ c : ∀ u, α u, (∀ u ∈ X, c u = v u) →
        0 < m.scm.dist.margAt Z c → 0 < m.scm.dist.margAt (X ∪ Z) c}
      {m : Model G α' | ∀ c : ∀ u, α' u, (∀ u ∈ X, c u = v' u) →
        0 < m.scm.dist.margAt Z c → 0 < m.scm.dist.margAt (X ∪ Z) c}
      O e (fun m => m.scm.effect X v Y v) (fun m => m.scm.effect X v' Y v') := by
  have hXYO : ∀ u ∈ X ∪ Y, u ∈ O := fun u hu => hO (mem_union_left _ hu)
  have hZO : ∀ u ∈ Z, u ∈ O := fun u hu => hO (mem_union_right _ hu)
  have hvr : ∀ u ∈ X ∪ Y, mergeRight O e u (v' u) = mergeLeft O u (v u) := fun u hu =>
    mergeRight_of_agree e (hXYO u hu) (hv u hu (hXYO u hu))
  refine identifiableAcross_of_identifiableFrom
    (identifiableFrom_effect_of_backDoor (fun u => mergeLeft O u (v u)) hbd hYZ hO) ?_ ?_ ?_ ?_
  · intro m hm c' hcX hZ
    exact backDoorPos_retype (M := m.scm) (mergeLeft_injective (α' := α')) (x := v)
      (x' := fun u => mergeLeft O u (v u)) (fun _ _ => rfl)
      (fun u hu => mergeLeft_surjective (hZO u hu)) hm c' hcX hZ
  · intro m hm c' hcX hZ
    exact backDoorPos_retype (M := m.scm) (mergeRight_injective e) (x := v')
      (x' := fun u => mergeLeft O u (v u)) (fun u hu => hvr u (mem_union_left _ hu))
      (fun u hu => mergeRight_surjective e (hZO u hu)) hm c' hcX hZ
  · exact fun m _ => effect_retype (mergeLeft_injective (α' := α')) (fun _ _ => rfl)
      fun _ _ => rfl
  · exact fun m _ => effect_retype (mergeRight_injective e)
      (fun u hu => hvr u (mem_union_left _ hu)) fun u hu => hvr u (mem_union_right _ hu)

/-- **Front-door adjustment across latent value types** (Pearl 2009, Theorem 3.3.4): if `Z`
satisfies the front-door criterion relative to `(X, Y)`, the observed set contains `X ∪ Y ∪ Z`,
and the values `v`, `v'` correspond through `e` on `X ∪ Y`, then a model with value types `α` and
a model with value types `α'`, both with a strictly positive law of `(X, Z)` and with the same
observed law, have the same effect `P(y | do(x))`, whatever the value types of the latent
vertices (in particular of the confounder of `X` and `Y`). -/
theorem identifiableAcross_effect_of_frontDoor {X Y Z : Finset V} (v : ∀ u, α u)
    (v' : ∀ u, α' u) (hfd : G.FrontDoor ↑X ↑Y ↑Z) (hO : X ∪ Y ∪ Z ⊆ O)
    (hv : ∀ u ∈ X ∪ Y, ∀ h : u ∈ O, e u h (v u) = v' u) :
    IdentifiableAcross
      {m : Model G α | ∀ c : ∀ u, α u, 0 < m.scm.dist.margAt (X ∪ Z) c}
      {m : Model G α' | ∀ c : ∀ u, α' u, 0 < m.scm.dist.margAt (X ∪ Z) c}
      O e (fun m => m.scm.effect X v Y v) (fun m => m.scm.effect X v' Y v') := by
  have hXYO : ∀ u ∈ X ∪ Y, u ∈ O := fun u hu => hO (mem_union_left _ hu)
  have hXZO : ∀ u ∈ X ∪ Z, u ∈ O := fun u hu => by
    rcases mem_union.1 hu with h | h
    · exact hO (mem_union_left _ (mem_union_left _ h))
    · exact hO (mem_union_right _ h)
  have hvr : ∀ u ∈ X ∪ Y, mergeRight O e u (v' u) = mergeLeft O u (v u) := fun u hu =>
    mergeRight_of_agree e (hXYO u hu) (hv u hu (hXYO u hu))
  refine identifiableAcross_of_identifiableFrom
    (identifiableFrom_effect_of_frontDoor (fun u => mergeLeft O u (v u)) hfd hO) ?_ ?_ ?_ ?_
  · intro m hm c'
    exact margAt_pos_retype (M := m.scm) (mergeLeft_injective (α' := α'))
      (fun u hu => mergeLeft_surjective (hXZO u hu)) hm c'
  · intro m hm c'
    exact margAt_pos_retype (M := m.scm) (mergeRight_injective e)
      (fun u hu => mergeRight_surjective e (hXZO u hu)) hm c'
  · exact fun m _ => effect_retype (mergeLeft_injective (α' := α')) (fun _ _ => rfl)
      fun _ _ => rfl
  · exact fun m _ => effect_retype (mergeRight_injective e)
      (fun u hu => hvr u (mem_union_left _ hu)) fun u hu => hvr u (mem_union_right _ hu)

end Applications

/-! ### Padding a model with independent noise -/

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The image of a product law under a coordinatewise map is the product of the images. -/
theorem _root_.CausalInference.FiniteDist.map_pi_coord {κ κ' : V → Type*}
    [∀ v, Fintype (κ v)] [∀ v, Fintype (κ' v)] [∀ v, DecidableEq (κ' v)] [DecidableEq V]
    (p : ∀ v, FiniteDist (κ v)) (f : ∀ v, κ v → κ' v) :
    (FiniteDist.pi p).map (fun ω v => f v (ω v)) = FiniteDist.pi fun v => (p v).map (f v) := by
  ext b
  rw [FiniteDist.map_apply_eq_prob, FiniteDist.pi_apply]
  have h : (univ.filter fun ω : ∀ v, κ v => (fun v => f v (ω v)) = b) =
      Fintype.piFinset fun v => univ.filter fun a => f v a = b v := by
    ext ω
    simp [funext_iff]
  rw [h, FiniteDist.prob_piFinset]
  rfl

section Pad

variable {α β : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)
  {η : V → Type*} [∀ v, Fintype (η v)]

/-- The model `M` **padded** with independent noise: every vertex gets an extra noise coordinate
`n v` with law `q v`, independent of everything else, and its value is `ι v a (n v)`, where `a`
is the value computed by the structural function of `M` from the parent values read back through
`π`. When `π v (ι v a n) = a`, the extra coordinates are ignored by every structural equation. -/
noncomputable def pad (q : ∀ v, FiniteDist (η v)) (ι : ∀ v, α v → η v → β v)
    (π : ∀ v, β v → α v) : SCM G β (fun v => ε v × η v) where
  acyclic := M.acyclic
  f v z en := ι v (M.f v (fun p => π p (z p)) en.1) en.2
  noise v := (M.noise v).prod (q v)

variable {M} {q : ∀ v, FiniteDist (η v)} {ι : ∀ v, α v → η v → β v} {π : ∀ v, β v → α v}
  (hπ : ∀ v a n, π v (ι v a n) = a)
include hπ

/-- Under `do(X := x')`, the solution of the padded model applies `ι` to the solution of
`do(X := x)` in `M` at the original noise coordinates, when `ι v (x v) n = x' v` on `X` for
every `n`. -/
theorem solve_pad_intervene {X : Finset V} {x : ∀ v, α v} {x' : ∀ v, β v}
    (hx : ∀ v ∈ X, ∀ n, ι v (x v) n = x' v) (u : ∀ v, ε v × η v) :
    ((M.pad q ι π).intervene X x').solve u =
      fun v => ι v ((M.intervene X x).solve (fun w => (u w).1) v) (u v).2 := by
  refine (((M.pad q ι π).intervene X x').eq_solve_of_isSolution
    ((M.pad q ι π).isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩)).symm
  · rw [M.solve_intervene_of_mem _ hv, hx v hv]
  · change _ = ι v (M.f v (fun p => _) (u v).1) (u v).2
    rw [M.solve_intervene_of_notMem _ hv]
    congr 2
    funext p
    exact (hπ p _ _).symm

omit [DecidableEq V] in
/-- The solution of the padded model. -/
theorem solve_pad (u : ∀ v, ε v × η v) :
    (M.pad q ι π).solve u = fun v => ι v (M.solve (fun w => (u w).1) v) (u v).2 := by
  classical
  have h := solve_pad_intervene (M := M) (q := q) hπ (X := ∅) (x := M.refConfig)
    (x' := (M.pad q ι π).solve u) (fun v hv => absurd hv (notMem_empty v)) u
  rwa [solve_intervene_empty, solve_intervene_empty] at h

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] [∀ v, Fintype (β v)]
  [∀ v, DecidableEq (β v)]

/-- Marginal masses of the padded model under an intervention: on a set `S` where the value
`ι v a n` determines `a` and the target `c' v` corresponds to `c v` whatever `n`, the mass is
that of `M`. -/
theorem margAt_pad_intervene {X : Finset V} {x : ∀ v, α v} {x' : ∀ v, β v}
    (hx : ∀ v ∈ X, ∀ n, ι v (x v) n = x' v) {S : Finset V} {c : ∀ v, α v} {c' : ∀ v, β v}
    (hc : ∀ v ∈ S, ∀ a n, ι v a n = c' v ↔ a = c v) :
    ((M.pad q ι π).intervene X x').dist.margAt S c' = (M.intervene X x).dist.margAt S c := by
  classical
  rw [margAt_dist, margAt_dist, noiseDist_intervene, noiseDist_intervene]
  have hfst : (M.pad q ι π).noiseDist.map (fun u w => (u w).1) = M.noiseDist := by
    change (FiniteDist.pi fun v => (M.noise v).prod (q v)).map (fun u w => (u w).1) = _
    rw [FiniteDist.map_pi_coord]
    simp only [FiniteDist.map_fst_prod]
    rfl
  rw [← hfst, FiniteDist.probOf_map]
  refine (M.pad q ι π).noiseDist.probOf_congr fun u => forall₂_congr fun v hv => ?_
  rw [solve_pad_intervene hπ hx]
  exact hc v hv _ _

/-- Marginal masses of the padded model. -/
theorem margAt_pad {S : Finset V} {c : ∀ v, α v} {c' : ∀ v, β v}
    (hc : ∀ v ∈ S, ∀ a n, ι v a n = c' v ↔ a = c v) :
    (M.pad q ι π).dist.margAt S c' = M.dist.margAt S c := by
  have h := margAt_pad_intervene (M := M) (q := q) hπ (X := ∅) (x := M.refConfig)
    (x' := c') (fun v hv => absurd hv (notMem_empty v)) hc
  rwa [dist_intervene_empty, dist_intervene_empty] at h

/-- **Padding preserves causal effects**: with `ι v (x v) n = x' v` on `X` for every `n`, and on
`Y` the value `ι v a n` equal to `y' v` exactly when `a = y v`, the effect
`P(Y = y' | do(X := x'))` in the padded model is `P(Y = y | do(X := x))` in `M`. -/
theorem effect_pad {X Y : Finset V} {x y : ∀ v, α v} {x' y' : ∀ v, β v}
    (hx : ∀ v ∈ X, ∀ n, ι v (x v) n = x' v) (hy : ∀ v ∈ Y, ∀ a n, ι v a n = y' v ↔ a = y v) :
    (M.pad q ι π).effect X x' Y y' = M.effect X x Y y :=
  margAt_pad_intervene hπ hx hy

/-- **Padding preserves strict positivity of the joint law**: if `M` has a strictly positive
joint law, every extra noise value has positive probability, and every value of `β v` is of the
form `ι v a n`, then the padded model has a strictly positive joint law. -/
theorem dist_pad_pos (hM : ∀ w, 0 < M.dist w) (hq : ∀ v n, 0 < q v n)
    (hs : ∀ v (b : β v), ∃ a n, ι v a n = b) (c' : ∀ v, β v) : 0 < (M.pad q ι π).dist c' := by
  classical
  choose a n hn using hs
  have hw := hM fun v => a v (c' v)
  rw [dist_apply, FiniteDist.prob] at hw
  obtain ⟨u, hu, hpos⟩ : ∃ u ∈ univ.filter fun u => M.solve u = fun v => a v (c' v),
      0 < M.noiseDist u := by
    by_contra hne
    push Not at hne
    exact (sum_nonpos hne).not_gt hw
  let un : ∀ v, ε v × η v := fun v => (u v, n v (c' v))
  have hsol : (M.pad q ι π).solve un = c' := by
    rw [solve_pad hπ]
    funext v
    change ι v (M.solve u v) (n v (c' v)) = c' v
    rw [(mem_filter.1 hu).2]
    exact hn v _
  rw [dist_apply, FiniteDist.prob]
  refine lt_of_lt_of_le ?_ (single_le_sum (fun _ _ => FiniteDist.nonneg _ _)
    (mem_filter.2 ⟨mem_univ un, hsol⟩))
  change 0 < ∏ v, ((M.noise v).prod (q v)) (un v)
  simp only [FiniteDist.prod_apply, prod_mul_distrib]
  exact mul_pos hpos (prod_pos fun v _ => hq v _)

end Pad

/-! ### A common value type that keeps strict positivity -/

section PadMerge

universe u

variable (O : Finset V) {α α' : V → Type u}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The padded merged value type of `α` and `α'` relative to `O`: `α v` at an observed vertex,
and the product `α v × α' v` at a latent vertex. -/
def PadType (α α' : V → Type u) (v : V) : Type u :=
  if v ∈ O then α v else α v × α' v

omit [Fintype V] [DecidableRel G.Adj] in
instance [∀ v, Fintype (α v)] [∀ v, Fintype (α' v)] (v : V) : Fintype (PadType O α α' v) := by
  unfold PadType
  split <;> infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
instance [∀ v, DecidableEq (α v)] [∀ v, DecidableEq (α' v)] (v : V) :
    DecidableEq (PadType O α α' v) := by
  unfold PadType
  split <;> infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
theorem padType_of_mem {v : V} (h : v ∈ O) : PadType O α α' v = α v := by
  simp [PadType, h]

omit [Fintype V] [DecidableRel G.Adj] in
theorem padType_of_notMem {v : V} (h : v ∉ O) : PadType O α α' v = (α v × α' v) := by
  simp [PadType, h]

variable [∀ v, Fintype (α v)] [∀ v, Fintype (α' v)]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The value of a vertex of the padded embedding of `α`: `a` on `O`, and off `O` the pair of
`a` with the value of `α' v` numbered `n`. -/
noncomputable def padLeft (v : V) (a : α v) (n : Fin (Fintype.card (α' v))) : PadType O α α' v :=
  if h : v ∈ O then cast (padType_of_mem O h).symm a
  else cast (padType_of_notMem O h).symm (a, (Fintype.equivFin (α' v)).symm n)

omit [Fintype V] [DecidableRel G.Adj] [∀ v, Fintype (α v)] [∀ v, Fintype (α' v)] in
/-- The read-back of the padded embedding of `α`: the first component off `O`. -/
def padLeftInv (v : V) (b : PadType O α α' v) : α v :=
  if h : v ∈ O then cast (padType_of_mem O h) b else (cast (padType_of_notMem O h) b).1

omit [Fintype V] [DecidableRel G.Adj] in
/-- The value of a vertex of the padded embedding of `α'`: `(e v)⁻¹ a'` on `O`, and off `O` the
pair of the value of `α v` numbered `n` with `a'`. -/
noncomputable def padRight (e : ∀ v, v ∈ O → α v ≃ α' v) (v : V) (a' : α' v)
    (n : Fin (Fintype.card (α v))) : PadType O α α' v :=
  if h : v ∈ O then cast (padType_of_mem O h).symm ((e v h).symm a')
  else cast (padType_of_notMem O h).symm ((Fintype.equivFin (α v)).symm n, a')

omit [Fintype V] [DecidableRel G.Adj] [∀ v, Fintype (α v)] [∀ v, Fintype (α' v)] in
/-- The read-back of the padded embedding of `α'`: the second component off `O`. -/
def padRightInv (e : ∀ v, v ∈ O → α v ≃ α' v) (v : V) (b : PadType O α α' v) : α' v :=
  if h : v ∈ O then e v h (cast (padType_of_mem O h) b) else (cast (padType_of_notMem O h) b).2

variable (e : ∀ v, v ∈ O → α v ≃ α' v)

omit [Fintype V] [DecidableRel G.Adj] [∀ v, Fintype (α v)] in
theorem padLeftInv_padLeft (v : V) (a : α v) (n : Fin (Fintype.card (α' v))) :
    padLeftInv O v (padLeft O v a n) = a := by
  by_cases h : v ∈ O <;> simp [padLeft, padLeftInv, h]

omit [Fintype V] [DecidableRel G.Adj] [∀ v, Fintype (α' v)] in
theorem padRightInv_padRight (v : V) (a' : α' v) (n : Fin (Fintype.card (α v))) :
    padRightInv O e v (padRight O e v a' n) = a' := by
  by_cases h : v ∈ O <;> simp [padRight, padRightInv, h]

omit [Fintype V] [DecidableRel G.Adj] [∀ v, Fintype (α v)] in
theorem padLeft_eq_iff {v : V} (hv : v ∈ O) {a : α v} {n : Fin (Fintype.card (α' v))}
    {b : PadType O α α' v} : padLeft O v a n = b ↔ a = padLeftInv O v b := by
  simp only [padLeft, padLeftInv, hv, dite_true]
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

omit [Fintype V] [DecidableRel G.Adj] [∀ v, Fintype (α' v)] in
theorem padRight_eq_iff {v : V} (hv : v ∈ O) {a' : α' v} {n : Fin (Fintype.card (α v))}
    {b : PadType O α α' v} : padRight O e v a' n = b ↔ a' = padRightInv O e v b := by
  simp only [padRight, padRightInv, hv, dite_true]
  constructor
  · rintro rfl
    simp
  · rintro rfl
    simp

omit [Fintype V] [DecidableRel G.Adj] [∀ v, Fintype (α v)] in
/-- On an observed vertex the padded embedding of `α` ignores the extra noise. -/
theorem padLeft_of_mem {v : V} (hv : v ∈ O) (a : α v) (n n' : Fin (Fintype.card (α' v))) :
    padLeft O v a n = padLeft O v a n' := by
  simp [padLeft, hv]

omit [Fintype V] [DecidableRel G.Adj] in
/-- On an observed vertex the two padded embeddings agree through `e`. -/
theorem padRight_of_agree {v : V} (hv : v ∈ O) {a : α v} {a' : α' v} (h : e v hv a = a')
    (n : Fin (Fintype.card (α' v))) (n' : Fin (Fintype.card (α v))) :
    padRight O e v a' n' = padLeft O v a n := by
  simp [padRight, padLeft, hv, ← h]

omit [Fintype V] [DecidableRel G.Adj] [∀ v, Fintype (α v)] in
/-- Every value of the padded type is a value of the padded embedding of `α`. -/
theorem padLeft_surjective [∀ v, Nonempty (α' v)] (v : V) (b : PadType O α α' v) :
    ∃ a n, padLeft O v a n = b := by
  by_cases h : v ∈ O
  · exact ⟨cast (padType_of_mem O h) b, ⟨0, Fintype.card_pos⟩, by simp [padLeft, h]⟩
  · refine ⟨(cast (padType_of_notMem O h) b).1,
      Fintype.equivFin (α' v) (cast (padType_of_notMem O h) b).2, ?_⟩
    simp [padLeft, h]

omit [Fintype V] [DecidableRel G.Adj] [∀ v, Fintype (α' v)] in
/-- Every value of the padded type is a value of the padded embedding of `α'`. -/
theorem padRight_surjective [∀ v, Nonempty (α v)] (v : V) (b : PadType O α α' v) :
    ∃ a' n, padRight O e v a' n = b := by
  by_cases h : v ∈ O
  · exact ⟨e v h (cast (padType_of_mem O h) b), ⟨0, Fintype.card_pos⟩, by simp [padRight, h]⟩
  · refine ⟨(cast (padType_of_notMem O h) b).2,
      Fintype.equivFin (α v) (cast (padType_of_notMem O h) b).1, ?_⟩
    simp [padRight, h]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [∀ v, Fintype (α v)]
  [∀ v, Fintype (α' v)] in
/-- A nonempty finite type has a nonempty numbering. -/
theorem nonempty_fin_card (γ : Type*) [Fintype γ] [Nonempty γ] :
    Nonempty (Fin (Fintype.card γ)) :=
  ⟨⟨0, Fintype.card_pos⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [∀ v, Fintype (α v)]
  [∀ v, Fintype (α' v)] in
/-- The uniform law on the numbering of a nonempty finite type has full support. -/
theorem uniform_fin_card_pos (γ : Type*) [Fintype γ] [Nonempty γ] (n : Fin (Fintype.card γ)) :
    0 < (@FiniteDist.uniform _ _ (nonempty_fin_card γ)) n := by
  rw [FiniteDist.uniform_apply]
  exact one_div_pos.2 (Nat.cast_pos.2 Fintype.card_pos)

omit [DecidableEq V] in
/-- The model `m` padded into `PadType O α α'`: every vertex gets an independent uniform noise
numbering the values of `α' v`, which supplies the second component at a latent vertex and is
ignored by every structural equation. -/
noncomputable def Model.padLeft (α' : V → Type u) [∀ v, Fintype (α' v)] [∀ v, Nonempty (α' v)]
    (m : Model G α) : Model G (PadType O α α') :=
  ⟨fun v => m.ε v × Fin (Fintype.card (α' v)),
    m.scm.pad (fun v => @FiniteDist.uniform _ _ (nonempty_fin_card (α' v))) (SCM.padLeft O)
      (SCM.padLeftInv O)⟩

omit [DecidableEq V] in
/-- The model `m` with value types `α'` padded into `PadType O α α'`, through `e` on `O`. -/
noncomputable def Model.padRight [∀ v, Nonempty (α v)] (m : Model G α') :
    Model G (PadType O α α') :=
  ⟨fun v => m.ε v × Fin (Fintype.card (α v)),
    m.scm.pad (fun v => @FiniteDist.uniform _ _ (nonempty_fin_card (α v))) (SCM.padRight O e)
      (SCM.padRightInv O e)⟩

variable [∀ v, DecidableEq (α v)] [∀ v, DecidableEq (α' v)]

/-- **Padding into `PadType` preserves strict positivity of the joint law.** -/
theorem dist_padLeft_pos [∀ v, Nonempty (α' v)] (m : Model G α) (hm : ∀ w, 0 < m.scm.dist w)
    (w : ∀ v, PadType O α α' v) : 0 < (m.padLeft O α').scm.dist w :=
  dist_pad_pos (padLeftInv_padLeft O) hm (fun v n => uniform_fin_card_pos (α' v) n)
    (padLeft_surjective O) w

/-- **Padding into `PadType` preserves strict positivity of the joint law.** -/
theorem dist_padRight_pos [∀ v, Nonempty (α v)] (m : Model G α') (hm : ∀ w, 0 < m.scm.dist w)
    (w : ∀ v, PadType O α α' v) : 0 < (m.padRight O e).scm.dist w :=
  dist_pad_pos (padRightInv_padRight O e) hm (fun v n => uniform_fin_card_pos (α v) n)
    (padRight_surjective O e) w

variable {O} {e}

/-- **Reduction to fixed value types through padding.** As
`SCM.identifiableAcross_of_identifiableFrom`, with the merged type `PadType O α α'` and the
padded embeddings `SCM.Model.padLeft`, `SCM.Model.padRight` in place of re-typing. -/
theorem identifiableAcross_of_identifiableFrom_pad [∀ v, Nonempty (α v)] [∀ v, Nonempty (α' v)]
    {R : Type*} {C : Set (Model G α)} {C' : Set (Model G α')}
    {Cβ : Set (Model G (PadType O α α'))} {Q : Model G α → R} {Q' : Model G α' → R}
    {Qβ : Model G (PadType O α α') → R} (hid : IdentifiableFrom Cβ O Qβ)
    (hC : ∀ m ∈ C, m.padLeft O α' ∈ Cβ) (hC' : ∀ m ∈ C', m.padRight O e ∈ Cβ)
    (hQ : ∀ m ∈ C, Qβ (m.padLeft O α') = Q m) (hQ' : ∀ m ∈ C', Qβ (m.padRight O e) = Q' m) :
    IdentifiableAcross C C' O e Q Q' := by
  intro m hm m' hm' hobs
  rw [← hQ m hm, ← hQ' m' hm']
  refine hid _ (hC m hm) _ (hC' m' hm') (marginal_eq_of_margAt_eq fun cβ => ?_)
  let c : ∀ v, α v := fun v => padLeftInv O v (cβ v)
  let c' : ∀ v, α' v := fun v => padRightInv O e v (cβ v)
  have hcc' : ∀ v (h : v ∈ O), e v h (c v) = c' v := fun v h => by
    simp [c, c', padLeftInv, padRightInv, h]
  change (m.scm.pad _ (padLeft O) (padLeftInv O)).dist.margAt O cβ =
    (m'.scm.pad _ (padRight O e) (padRightInv O e)).dist.margAt O cβ
  rw [margAt_pad (padLeftInv_padLeft O) (c := c) fun v hv _ _ => padLeft_eq_iff O hv,
    margAt_pad (padRightInv_padRight O e) (c := c') fun v hv _ _ => padRight_eq_iff O e hv]
  exact hobs c c' hcc'

/-- **Reduction for classes requiring a strictly positive joint law.** If `Qβ` is identifiable
from `O` among the models with value types `PadType O α α'` and a strictly positive joint law,
and `Q`, `Q'` are its values at the padded models, then `Q` and `Q'` are identifiable from `O`
across the value types `α`, `α'` among the models with a strictly positive joint law. -/
theorem identifiableAcross_pos_of_identifiableFrom [∀ v, Nonempty (α v)]
    [∀ v, Nonempty (α' v)] {R : Type*} {Q : Model G α → R} {Q' : Model G α' → R}
    {Qβ : Model G (PadType O α α') → R}
    (hid : IdentifiableFrom {m : Model G (PadType O α α') | ∀ w, 0 < m.scm.dist w} O Qβ)
    (hQ : ∀ m : Model G α, (∀ w, 0 < m.scm.dist w) → Qβ (m.padLeft O α') = Q m)
    (hQ' : ∀ m : Model G α', (∀ w, 0 < m.scm.dist w) → Qβ (m.padRight O e) = Q' m) :
    IdentifiableAcross {m : Model G α | ∀ w, 0 < m.scm.dist w}
      {m : Model G α' | ∀ w, 0 < m.scm.dist w} O e Q Q' :=
  identifiableAcross_of_identifiableFrom_pad hid (fun m hm => dist_padLeft_pos O m hm)
    (fun m hm => dist_padRight_pos O e m hm) hQ hQ'

/-- **Causal effects among strictly positive models across latent value types.** Let `X ∪ Y` be
observed and the values correspond through `e` on `X ∪ Y`. If the effect of `X` on `Y` is
identifiable from `O` among the models with value types `PadType O α α'` and a strictly positive
joint law, at all values, then a model with value types `α` and a model with value types `α'`,
both with a strictly positive joint law and the same observed law, have the same effect. -/
theorem identifiableAcross_effect_pos {X Y : Finset V} (hXO : X ⊆ O) (hYO : Y ⊆ O)
    {x y : ∀ v, α v} {x' y' : ∀ v, α' v} (hx : ∀ v ∈ X, ∀ h : v ∈ O, e v h (x v) = x' v)
    (hy : ∀ v ∈ Y, ∀ h : v ∈ O, e v h (y v) = y' v)
    (hid : ∀ xβ yβ : ∀ v, PadType O α α' v,
      IdentifiableFrom {m : Model G (PadType O α α') | ∀ w, 0 < m.scm.dist w} O
        (fun m => m.scm.effect X xβ Y yβ)) :
    IdentifiableAcross {m : Model G α | ∀ w, 0 < m.scm.dist w}
      {m : Model G α' | ∀ w, 0 < m.scm.dist w} O e (fun m => m.scm.effect X x Y y)
      (fun m => m.scm.effect X x' Y y') := by
  refine identifiableAcross_of_nonempty fun hα hα' => ?_
  have : ∀ v, Nonempty (α v) := hα
  have : ∀ v, Nonempty (α' v) := hα'
  let n₀ : ∀ v, Fin (Fintype.card (α' v)) := fun v => ⟨0, Fintype.card_pos⟩
  refine identifiableAcross_pos_of_identifiableFrom
    (hid (fun v => padLeft O v (x v) (n₀ v)) (fun v => padLeft O v (y v) (n₀ v))) ?_ ?_
  · intro m _
    refine effect_pad (padLeftInv_padLeft O) (fun v hv n => padLeft_of_mem O (hXO hv) _ _ _)
      fun v hv a n => ?_
    rw [padLeft_eq_iff O (hYO hv), padLeftInv_padLeft]
  · intro m _
    refine effect_pad (padRightInv_padRight O e)
      (fun v hv n => padRight_of_agree O e (hXO hv) (hx v hv _) _ _) fun v hv a n => ?_
    rw [padRight_eq_iff O e (hYO hv), ← padRight_of_agree O e (hYO hv) (hy v hv _) (n₀ v) n,
      padRightInv_padRight]

end PadMerge

/-! ### Value type families in different universes -/

section Universes

universe u u'

variable {α : V → Type u} {α' : V → Type u'} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
  [∀ v, Fintype (α' v)] [∀ v, DecidableEq (α' v)] {O : Finset V}
  (e : ∀ v, v ∈ O → α v ≃ α' v)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)] [∀ v, Fintype (α' v)] [∀ v, DecidableEq (α' v)] in
/-- The equivalences `e` on `O`, lifted to the common universe `max u u'`. -/
def liftEquiv : ∀ v, v ∈ O → ULift.{u'} (α v) ≃ ULift.{u} (α' v) :=
  fun v h => Equiv.ulift.trans ((e v h).trans Equiv.ulift.symm)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)] [∀ v, Fintype (α' v)] [∀ v, DecidableEq (α' v)] in
@[simp] theorem liftEquiv_up {v : V} (h : v ∈ O) (a : α v) :
    liftEquiv e v h (ULift.up a) = ULift.up (e v h a) := rfl

/-- **Reduction to fixed value types, families in different universes.** The merged value type
is formed from the lifts of `α` and `α'` to the universe `max u u'`; otherwise as
`SCM.identifiableAcross_of_identifiableFrom`. -/
theorem identifiableAcross_of_identifiableFrom_ulift {R : Type*} {C : Set (Model G α)}
    {C' : Set (Model G α')}
    {Cβ : Set (Model G (MergeType O (fun v => ULift.{u'} (α v)) (fun v => ULift.{u} (α' v))))}
    {Q : Model G α → R} {Q' : Model G α' → R}
    {Qβ : Model G (MergeType O (fun v => ULift.{u'} (α v)) (fun v => ULift.{u} (α' v))) → R}
    (hid : IdentifiableFrom Cβ O Qβ)
    (hC : ∀ m ∈ C, m.retype (fun v a => mergeLeft O v (ULift.up a)) ∈ Cβ)
    (hC' : ∀ m ∈ C', m.retype (fun v a => mergeRight O (liftEquiv e) v (ULift.up a)) ∈ Cβ)
    (hQ : ∀ m ∈ C, Qβ (m.retype fun v a => mergeLeft O v (ULift.up a)) = Q m)
    (hQ' : ∀ m ∈ C', Qβ (m.retype fun v a => mergeRight O (liftEquiv e) v (ULift.up a)) = Q' m) :
    IdentifiableAcross C C' O e Q Q' :=
  identifiableAcross_of_embed (fun v => (mergeLeft_injective v).comp ULift.up_injective)
    (fun v => (mergeRight_injective _ v).comp ULift.up_injective)
    (fun _ hv => (mergeLeft_surjective hv).comp ULift.up_surjective)
    (fun _ h _ => mergeRight_of_agree (liftEquiv e) h rfl) hid hC hC' hQ hQ'

/-- **Adjustment for direct causes across latent value types, any universes**: as
`SCM.identifiableAcross_effect_singleton_of_subset`, with `α` and `α'` in independent
universes. -/
theorem identifiableAcross_effect_singleton_of_subset_ulift (i : V) {x : ∀ v, α v}
    {x' : ∀ v, α' v} {Y : Finset V} {y : ∀ v, α v} {y' : ∀ v, α' v}
    (hO : insert i (G.parentsFinset i) ∪ Y ⊆ O) (hx : ∀ h : i ∈ O, e i h (x i) = x' i)
    (hy : ∀ v ∈ Y, ∀ h : v ∈ O, e v h (y v) = y' v) :
    IdentifiableAcross
      {m : Model G α | ∀ z : (∀ u : G.parentsFinset i, α u),
        0 < m.scm.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) →
        0 < m.scm.dist.probOf (fun w => w i = x i ∧ (G.parentsFinset i).restrict w = z)}
      {m : Model G α' | ∀ z : (∀ u : G.parentsFinset i, α' u),
        0 < m.scm.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) →
        0 < m.scm.dist.probOf (fun w => w i = x' i ∧ (G.parentsFinset i).restrict w = z)}
      O e (fun m => m.scm.effect {i} x Y y) (fun m => m.scm.effect {i} x' Y y') := by
  refine identifiableAcross_of_retype (ι := fun _ a => ULift.up.{u'} a)
    (ι' := fun _ a => ULift.up.{u} a) (fun _ => ULift.up_injective) (fun _ => ULift.up_injective)
    (fun _ _ => ULift.up_surjective) (fun _ _ _ => rfl)
    (identifiableAcross_effect_singleton_of_subset (liftEquiv e) i
      (x := fun v => ULift.up (x v)) (x' := fun v => ULift.up (x' v))
      (y := fun v => ULift.up (y v)) (y' := fun v => ULift.up (y' v)) hO
      (fun h => congrArg ULift.up (hx h)) fun v hv h => congrArg ULift.up (hy v hv h))
    ?_ ?_ ?_ ?_
  · intro m hm z' hz'
    exact overlap_retype (M := m.scm) (fun _ => ULift.up_injective) i (x := x)
      (x' := fun v => ULift.up (x v)) rfl (fun _ _ => ULift.up_surjective) hm z' hz'
  · intro m hm z' hz'
    exact overlap_retype (M := m.scm) (fun _ => ULift.up_injective) i (x := x')
      (x' := fun v => ULift.up (x' v)) rfl (fun _ _ => ULift.up_surjective) hm z' hz'
  · exact fun m _ => effect_retype (fun _ => ULift.up_injective) (fun _ _ => rfl) fun _ _ => rfl
  · exact fun m _ => effect_retype (fun _ => ULift.up_injective) (fun _ _ => rfl) fun _ _ => rfl

/-- **Back-door adjustment across latent value types, any universes**: as
`SCM.identifiableAcross_effect_of_backDoor`, with `α` and `α'` in independent universes. -/
theorem identifiableAcross_effect_of_backDoor_ulift {X Y Z : Finset V} (v : ∀ u, α u)
    (v' : ∀ u, α' u) (hbd : G.BackDoor ↑X ↑Y ↑Z) (hYZ : Disjoint Y Z) (hO : X ∪ Y ∪ Z ⊆ O)
    (hv : ∀ u ∈ X ∪ Y, ∀ h : u ∈ O, e u h (v u) = v' u) :
    IdentifiableAcross
      {m : Model G α | ∀ c : ∀ u, α u, (∀ u ∈ X, c u = v u) →
        0 < m.scm.dist.margAt Z c → 0 < m.scm.dist.margAt (X ∪ Z) c}
      {m : Model G α' | ∀ c : ∀ u, α' u, (∀ u ∈ X, c u = v' u) →
        0 < m.scm.dist.margAt Z c → 0 < m.scm.dist.margAt (X ∪ Z) c}
      O e (fun m => m.scm.effect X v Y v) (fun m => m.scm.effect X v' Y v') := by
  refine identifiableAcross_of_retype (ι := fun _ a => ULift.up.{u'} a)
    (ι' := fun _ a => ULift.up.{u} a) (fun _ => ULift.up_injective) (fun _ => ULift.up_injective)
    (fun _ _ => ULift.up_surjective) (fun _ _ _ => rfl)
    (identifiableAcross_effect_of_backDoor (liftEquiv e) (fun u => ULift.up (v u))
      (fun u => ULift.up (v' u)) hbd hYZ hO fun u hu h => congrArg ULift.up (hv u hu h))
    ?_ ?_ ?_ ?_
  · intro m hm c' hcX hZ
    exact backDoorPos_retype (M := m.scm) (fun _ => ULift.up_injective) (x := v)
      (x' := fun u => ULift.up (v u)) (fun _ _ => rfl) (fun _ _ => ULift.up_surjective) hm c'
      hcX hZ
  · intro m hm c' hcX hZ
    exact backDoorPos_retype (M := m.scm) (fun _ => ULift.up_injective) (x := v')
      (x' := fun u => ULift.up (v' u)) (fun _ _ => rfl) (fun _ _ => ULift.up_surjective) hm c'
      hcX hZ
  · exact fun m _ => effect_retype (fun _ => ULift.up_injective) (fun _ _ => rfl) fun _ _ => rfl
  · exact fun m _ => effect_retype (fun _ => ULift.up_injective) (fun _ _ => rfl) fun _ _ => rfl

/-- **Front-door adjustment across latent value types, any universes**: as
`SCM.identifiableAcross_effect_of_frontDoor`, with `α` and `α'` in independent universes. -/
theorem identifiableAcross_effect_of_frontDoor_ulift {X Y Z : Finset V} (v : ∀ u, α u)
    (v' : ∀ u, α' u) (hfd : G.FrontDoor ↑X ↑Y ↑Z) (hO : X ∪ Y ∪ Z ⊆ O)
    (hv : ∀ u ∈ X ∪ Y, ∀ h : u ∈ O, e u h (v u) = v' u) :
    IdentifiableAcross
      {m : Model G α | ∀ c : ∀ u, α u, 0 < m.scm.dist.margAt (X ∪ Z) c}
      {m : Model G α' | ∀ c : ∀ u, α' u, 0 < m.scm.dist.margAt (X ∪ Z) c}
      O e (fun m => m.scm.effect X v Y v) (fun m => m.scm.effect X v' Y v') := by
  refine identifiableAcross_of_retype (ι := fun _ a => ULift.up.{u'} a)
    (ι' := fun _ a => ULift.up.{u} a) (fun _ => ULift.up_injective) (fun _ => ULift.up_injective)
    (fun _ _ => ULift.up_surjective) (fun _ _ _ => rfl)
    (identifiableAcross_effect_of_frontDoor (liftEquiv e) (fun u => ULift.up (v u))
      (fun u => ULift.up (v' u)) hfd hO fun u hu h => congrArg ULift.up (hv u hu h))
    ?_ ?_ ?_ ?_
  · intro m hm c'
    exact margAt_pos_retype (M := m.scm) (fun _ => ULift.up_injective)
      (fun _ _ => ULift.up_surjective) hm c'
  · intro m hm c'
    exact margAt_pos_retype (M := m.scm) (fun _ => ULift.up_injective)
      (fun _ _ => ULift.up_surjective) hm c'
  · exact fun m _ => effect_retype (fun _ => ULift.up_injective) (fun _ _ => rfl) fun _ _ => rfl
  · exact fun m _ => effect_retype (fun _ => ULift.up_injective) (fun _ _ => rfl) fun _ _ => rfl

/-- **Causal effects among strictly positive models, any universes**: as
`SCM.identifiableAcross_effect_pos`, with `α` and `α'` in independent universes; the padded
merged type is formed from their lifts to the universe `max u u'`. -/
theorem identifiableAcross_effect_pos_ulift {X Y : Finset V} (hXO : X ⊆ O) (hYO : Y ⊆ O)
    {x y : ∀ v, α v} {x' y' : ∀ v, α' v} (hx : ∀ v ∈ X, ∀ h : v ∈ O, e v h (x v) = x' v)
    (hy : ∀ v ∈ Y, ∀ h : v ∈ O, e v h (y v) = y' v)
    (hid : ∀ xβ yβ : ∀ v, PadType O (fun v => ULift.{u'} (α v)) (fun v => ULift.{u} (α' v)) v,
      IdentifiableFrom {m : Model G (PadType O (fun v => ULift.{u'} (α v))
        (fun v => ULift.{u} (α' v))) | ∀ w, 0 < m.scm.dist w} O
        (fun m => m.scm.effect X xβ Y yβ)) :
    IdentifiableAcross {m : Model G α | ∀ w, 0 < m.scm.dist w}
      {m : Model G α' | ∀ w, 0 < m.scm.dist w} O e (fun m => m.scm.effect X x Y y)
      (fun m => m.scm.effect X x' Y y') := by
  refine identifiableAcross_of_retype (ι := fun _ a => ULift.up.{u'} a)
    (ι' := fun _ a => ULift.up.{u} a) (fun _ => ULift.up_injective) (fun _ => ULift.up_injective)
    (fun _ _ => ULift.up_surjective) (fun _ _ _ => rfl)
    (identifiableAcross_effect_pos (e := liftEquiv e) hXO hYO (x := fun v => ULift.up (x v))
      (y := fun v => ULift.up (y v)) (x' := fun v => ULift.up (x' v))
      (y' := fun v => ULift.up (y' v)) (fun v hv h => congrArg ULift.up (hx v hv h))
      (fun v hv h => congrArg ULift.up (hy v hv h)) hid) ?_ ?_ ?_ ?_
  · exact fun m hm => dist_pos_retype (M := m.scm) (fun _ => ULift.up_injective)
      (fun _ => ULift.up_surjective) hm
  · exact fun m hm => dist_pos_retype (M := m.scm) (fun _ => ULift.up_injective)
      (fun _ => ULift.up_surjective) hm
  · exact fun m _ => effect_retype (fun _ => ULift.up_injective) (fun _ _ => rfl) fun _ _ => rfl
  · exact fun m _ => effect_retype (fun _ => ULift.up_injective) (fun _ _ => rfl) fun _ _ => rfl

end Universes

end SCM

end CausalInference
