/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Adjustment
public import CausalInference.SCM.TwinNetwork

/-!
# Conditional ignorability from the back-door criterion

The file `CausalInference.SCM.TwinNetwork` proves the counterfactual reading of the back-door
criterion only for the parents of the treatment. This file proves it for every set `Z` that
satisfies the back-door criterion `Digraph.BackDoor G X Y Z`: under the noise law, the potential
response `Y_x` is conditionally independent of the factual treatment given the factual `Z`, and
so is the whole family `(Y_{x_k})_k` of potential responses under several treatment values.

## The world of an intervention

The proof does not go through the twin network, nor through a separate interventional law as
in `CausalInference.SCM.InstrumentCounterfactual`. It uses one structural model whose solution
carries the variables of the single world of `do(A := a)` (Richardson and Robins 2013):

* `SCM.world M A a u v`: the value of `v` in the world of `do(A := a)`, defined as the value of
  `v` under the intervention on `A` with `v` itself removed. For `v ∉ A` this is the potential
  response `V_a(u)`; for `v ∈ A` it is the natural value of the treatment `v` when the other
  treatments are set to `a`.
* `SCM.worldModel M A a`: a structural model on `G.deleteOutgoing A` (the graph with every edge
  out of `A` removed) whose equations are those of `M` with the parents in `A` replaced by the
  constants `a`. Its solution is `SCM.world M A a` (`SCM.worldModel_solve`), so the law of the
  world variables factorizes according to `G.deleteOutgoing A` and has the global Markov
  property there (`SCM.condIndepFun_world_of_dSep`).
* `SCM.familyModel M A x`: the same construction for a family `x : κ → ∀ v, α v` of treatment
  values at once, with value type `κ → α v` at `v` (`SCM.familyModel_solve`). Its global Markov
  property gives joint statements about all worlds `(V_{x_k})_k` together
  (`SCM.condIndepFun_family_of_dSep`). These cross-world statements hold for the Markovian models
  of the library, whose noises are independent.

## Main results

* `SCM.condIndepFun_response_of_backDoor`: if `Z` satisfies the back-door criterion relative to
  `(X, Y)`, then the factual treatments `X` are conditionally independent, given the factual
  `Z`, of the whole response `a ↦ Y_a` of `Y` to all treatment values. The treatment set is
  arbitrary. The corollaries: `SCM.condIndepFun_family_of_backDoor` for a finite family of
  values (`(Y_{x_k})_k ⫫ X | Z`), `SCM.condIndepFun_potentialResponse_of_backDoor` for one value
  (`Y_x ⫫ X | Z`), `SCM.condIndepFun_potentialResponse_pair_of_backDoor` for two
  (`(Y_x, Y_x') ⫫ X | Z`), and the `_singleton` versions for one treatment vertex.
* `SCM.condIndepFun_world_of_backDoor`: the single-world statement, `Y_x` conditionally
  independent of the world treatments given `Z`, read off the graph of the world.
* `SCM.world_agree_iff`: the world treatments take the values `x` exactly when the factual
  treatments do. This is what turns the statement about the world treatments into one about the
  factual treatments: the factual treatments are a function of the world treatments of all
  worlds together.
* `SCM.backdoor_stratum_cf`, `SCM.effect_eq_sum_of_backDoor_cf`: the per-stratum identity and
  the back-door adjustment formula of `CausalInference.SCM.Adjustment`, derived a second time
  from the counterfactual independence and consistency, for an arbitrary treatment set.
  `SCM.effect_eq_sum_of_backDoor_routes_agree` records that the counterfactual route and the
  route through the rules of the do-calculus give the same value.

## References

* T. S. Richardson and J. M. Robins (2013), *Single World Intervention Graphs (SWIGs): A
  Unification of the Counterfactual and Graphical Approaches to Causality*.
* J. Pearl (2009), *Causality: Models, Reasoning, and Inference*, 2nd edition, section 3.3.1
  and section 11.3.2.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-! ### The world of an intervention -/

/-- The value of `v` in the single world of the intervention `do(A := x)`: the value of `v`
under the intervention on `A` with `v` itself removed. For `v ∉ A` it is the potential response
`V_x(u)`; for `v ∈ A` it is the natural value of `v` when the other members of `A` are set to
`x`. -/
noncomputable def world (A : Finset V) (x : ∀ v, α v) (u : ∀ v, ε v) : ∀ v, α v :=
  fun v => (M.intervene (A.erase v) x).solve u v

theorem world_apply (A : Finset V) (x : ∀ v, α v) (u : ∀ v, ε v) (v : V) :
    M.world A x u v = (M.intervene (A.erase v) x).solve u v := rfl

/-- Outside `A`, the world value is the potential response under `do(A := x)`. -/
theorem world_of_notMem {A : Finset V} (x : ∀ v, α v) (u : ∀ v, ε v) {v : V} (hv : v ∉ A) :
    M.world A x u v = (M.intervene A x).solve u v := by
  rw [world_apply, erase_eq_of_notMem hv]

/-- **Consistency for nondescendants**: a vertex that is not a descendant of the other members
of `A` takes its factual value in the world of `do(A := x)`. -/
theorem world_of_notMem_descendantsOf {A : Finset V} (x : ∀ v, α v) (u : ∀ v, ε v) {v : V}
    (hv : v ∉ G.descendantsOf ↑(A.erase v)) : M.world A x u v = M.solve u v :=
  M.solve_intervene_of_notMem_descendantsOf u hv

/-- Removing `w` from the intervention set does not change a vertex `v` that is not a
descendant of `w`. -/
theorem solve_intervene_erase_of_not_reflTransGen {A : Finset V} (x : ∀ v, α v)
    (u : ∀ v, ε v) {w v : V} (h : ¬ Relation.ReflTransGen G.Adj w v) :
    (M.intervene (A.erase w) x).solve u v = (M.intervene A x).solve u v := by
  by_cases hw : w ∈ A
  · have e : (M.intervene A x).solve = ((M.intervene (A.erase w) x).intervene {w} x).solve := by
      rw [solve_intervene_intervene]
      simp only [ite_self]
      rw [union_comm, ← insert_eq, insert_erase hw]
    rw [e]
    refine ((M.intervene (A.erase w) x).solve_intervene_of_notMem_descendantsOf u ?_).symm
    intro hmem
    obtain ⟨s, hs, hsv⟩ := Digraph.mem_descendantsOf.1 hmem
    rw [coe_singleton, Set.mem_singleton_iff] at hs
    subst hs
    exact h (hsv.lift id fun _ _ hab => hab.1)
  · rw [erase_eq_of_notMem hw]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In an acyclic graph a parent of `v` is not a descendant of `v`. -/
theorem not_reflTransGen_of_adj (hG : G.IsAcyclic) {p v : V} (h : G.Adj p v) :
    ¬ Relation.ReflTransGen G.Adj v p :=
  fun h' => hG v (Relation.TransGen.tail' h' h)

/-- **The structural equation of the world**: the world value of `v` is the structural function
of `v` applied to the world values of its parents, with the parents in `A` replaced by their
assigned values. -/
theorem world_eq (A : Finset V) (x : ∀ v, α v) (u : ∀ v, ε v) (v : V) :
    M.world A x u v =
      M.f v (fun p => if p.1 ∈ A then x p.1 else M.world A x u p.1) (u v) := by
  rw [world_apply, M.solve_intervene_of_notMem u (notMem_erase v A)]
  congr 1
  funext p
  have hpv : G.Adj p.1 v := Digraph.mem_parentsFinset.1 p.2
  simp only [Finset.restrict]
  split_ifs with hp
  · have hne : p.1 ≠ v := fun h => M.acyclic.irrefl v (by rw [h] at hpv; exact hpv)
    exact M.solve_intervene_of_mem u (mem_erase.2 ⟨hne, hp⟩)
  · rw [M.world_of_notMem x u hp]
    exact M.solve_intervene_erase_of_not_reflTransGen x u (not_reflTransGen_of_adj M.acyclic hpv)

/-- **Consistency of the world treatments**: the members of `A` take the values `x` in the world
of `do(A := x)` exactly when they take them without intervention. The world value of a
treatment is its natural value under the intervention on the other treatments, so for a
treatment that descends from another one it differs from the factual value in general; the
two agree on the event that every treatment takes its assigned value. -/
theorem world_agree_iff (A : Finset V) (x : ∀ v, α v) (u : ∀ v, ε v) :
    (∀ v ∈ A, M.world A x u v = x v) ↔ ∀ v ∈ A, M.solve u v = x v := by
  constructor
  · intro h
    have hsol : M.IsSolution u ((M.intervene A x).solve u) := by
      intro v
      by_cases hv : v ∈ A
      · rw [M.solve_intervene_of_mem u hv, ← h v hv, world_apply,
          M.solve_intervene_of_notMem u (notMem_erase v A)]
        congr 1
        funext p
        have hpv : G.Adj p.1 v := Digraph.mem_parentsFinset.1 p.2
        simp only [Finset.restrict]
        exact M.solve_intervene_erase_of_not_reflTransGen x u
          (not_reflTransGen_of_adj M.acyclic hpv)
      · exact M.solve_intervene_of_notMem u hv
    intro v hv
    rw [← M.eq_solve_of_isSolution hsol]
    exact M.solve_intervene_of_mem u hv
  · intro h v hv
    rw [world_apply, M.solve_intervene_of_agree fun w hw => h w (mem_of_mem_erase hw)]
    exact h v hv

/-- A parent of `v` outside `A` is a parent of `v` in `G.deleteOutgoing A`. -/
theorem mem_parentsFinset_deleteOutgoing {A : Finset V} {v : V} (p : G.parentsFinset v)
    (hp : p.1 ∉ A) : p.1 ∈ (G.deleteOutgoing ↑A).parentsFinset v :=
  Digraph.mem_parentsFinset.2 ⟨Digraph.mem_parentsFinset.1 p.2, hp⟩

/-- The **world model** of `do(A := x)`: a structural model on `G.deleteOutgoing A`, the graph
with every edge out of `A` removed, with the noises of `M`. The equation of each vertex is its
equation in `M`, with the parents in `A` replaced by the constants `x`. In the language of
single world intervention graphs, each treatment is split into a random half, which keeps the
edges into the treatment, and a fixed half, the constant, which keeps the edges out of it; the
graph of the model is the graph of the random vertices. -/
def worldModel (A : Finset V) (x : ∀ v, α v) : SCM (G.deleteOutgoing ↑A) α ε where
  acyclic := M.acyclic.deleteOutgoing
  f v z e := M.f v (fun p => if hp : p.1 ∈ A then x p.1 else
    z ⟨p.1, mem_parentsFinset_deleteOutgoing p hp⟩) e
  noise := M.noise

@[simp] theorem noiseDist_worldModel (A : Finset V) (x : ∀ v, α v) :
    (M.worldModel A x).noiseDist = M.noiseDist := rfl

/-- The solution of the world model is the world of `do(A := x)`. -/
theorem worldModel_solve (A : Finset V) (x : ∀ v, α v) (u : ∀ v, ε v) :
    (M.worldModel A x).solve u = M.world A x u := by
  refine ((M.worldModel A x).eq_solve_of_isSolution fun v => ?_).symm
  rw [M.world_eq A x u v]
  change _ = M.f v _ (u v)
  congr 1

/-- The **family model** of the interventions `do(A := x k)`, `k : κ`: a structural model on
`G.deleteOutgoing A` with value type `κ → α v` at `v`, whose coordinate `k` follows the world
model of `do(A := x k)`. All coordinates read the same noise, so its law is the joint law of
all the worlds at once. -/
def familyModel (A : Finset V) {κ : Type*} (x : κ → ∀ v, α v) :
    SCM (G.deleteOutgoing ↑A) (fun v => κ → α v) ε where
  acyclic := M.acyclic.deleteOutgoing
  f v z e := fun k => M.f v (fun p => if hp : p.1 ∈ A then x k p.1 else
    z ⟨p.1, mem_parentsFinset_deleteOutgoing p hp⟩ k) e
  noise := M.noise

@[simp] theorem noiseDist_familyModel (A : Finset V) {κ : Type*} (x : κ → ∀ v, α v) :
    (M.familyModel A x).noiseDist = M.noiseDist := rfl

/-- The solution of the family model is the family of the worlds of `do(A := x k)`. -/
theorem familyModel_solve (A : Finset V) {κ : Type*} (x : κ → ∀ v, α v) (u : ∀ v, ε v) :
    (M.familyModel A x).solve u = fun v k => M.world A (x k) u v := by
  refine ((M.familyModel A x).eq_solve_of_isSolution fun v => ?_).symm
  funext k
  rw [M.world_eq A (x k) u v]
  change _ = M.f v _ (u v)
  congr 1

/-! ### The global Markov property of the worlds -/

omit [DecidableRel G.Adj] in
/-- The global Markov property of a model, for the random variables of the noise: a
d-separation in the graph gives the conditional independence of the corresponding coordinates
of the solution under the noise law. -/
theorem condIndepFun_solve_of_dSep {H : Digraph V} [DecidableRel H.Adj] {β : V → Type*}
    [∀ v, Finite (β v)] [∀ v, DecidableEq (β v)] (N : SCM H β ε) {S T C : Finset V}
    (h : H.DSep ↑S ↑T ↑C) :
    N.noiseDist.CondIndepFun (fun u => S.restrict (N.solve u)) (fun u => T.restrict (N.solve u))
      (fun u => C.restrict (N.solve u)) :=
  have : ∀ v, Fintype (β v) := fun _ => Fintype.ofFinite _
  (FiniteDist.condIndepFun_map_iff N.noiseDist N.solve (S.restrict (π := β))
    (T.restrict (π := β)) (C.restrict (π := β))).1 (N.factorizes.condIndep_of_dSep N.acyclic h)

section Finite

variable [∀ v, Finite (α v)] [∀ v, DecidableEq (α v)]

/-- **Global Markov property of the world**: if `S` and `T` are d-separated by `C` in
`G.deleteOutgoing A`, then under the noise law the world variables of `S` and of `T` in the
world of `do(A := x)` are conditionally independent given those of `C`. -/
theorem condIndepFun_world_of_dSep (A : Finset V) (x : ∀ v, α v) {S T C : Finset V}
    (h : (G.deleteOutgoing ↑A).DSep ↑S ↑T ↑C) :
    M.noiseDist.CondIndepFun (fun u => S.restrict (M.world A x u))
      (fun u => T.restrict (M.world A x u)) (fun u => C.restrict (M.world A x u)) := by
  have : ∀ v, Fintype (α v) := fun _ => Fintype.ofFinite _
  have h' := (M.worldModel A x).condIndepFun_solve_of_dSep h
  simp only [worldModel_solve, noiseDist_worldModel] at h'
  exact h'

/-- **Global Markov property of a family of worlds**: if `S` and `T` are d-separated by `C` in
`G.deleteOutgoing A`, then under the noise law the families of world variables
`(S in the world of do(A := x k))_k` and `(T ...)_k` are conditionally independent given the
family for `C`. -/
theorem condIndepFun_family_of_dSep (A : Finset V) {κ : Type*} [Fintype κ]
    (x : κ → ∀ v, α v) {S T C : Finset V} (h : (G.deleteOutgoing ↑A).DSep ↑S ↑T ↑C) :
    M.noiseDist.CondIndepFun (fun u (v : S) k => M.world A (x k) u v)
      (fun u (v : T) k => M.world A (x k) u v) (fun u (v : C) k => M.world A (x k) u v) := by
  classical
  have : ∀ v, Fintype (α v) := fun _ => Fintype.ofFinite _
  have h' := (M.familyModel A x).condIndepFun_solve_of_dSep h
  simp only [familyModel_solve, noiseDist_familyModel] at h'
  exact h'

/-! ### Conditional ignorability from the back-door criterion -/

omit [Fintype V] [DecidableRel G.Adj] [∀ v, Fintype (ε v)] [∀ v, Finite (α v)]
  [∀ v, DecidableEq (α v)] in
/-- A member of a back-door set is not a descendant of any subset of the treatments. -/
theorem notMem_descendantsOf_erase_of_backDoor {X Y Z : Finset V} (hbd : G.BackDoor ↑X ↑Y ↑Z)
    {v : V} (hv : v ∈ Z) (w : V) : v ∉ G.descendantsOf ↑(X.erase w) := fun h =>
  hbd.1 v (mem_coe.2 hv) (Digraph.descendantsOf_mono (coe_subset.2 (erase_subset w X)) h)

omit [∀ v, Finite (α v)] in
/-- **Conditional ignorability of all potential responses at once.** If `Z` satisfies the
back-door criterion relative to `(X, Y)`, then under the noise law the factual treatments `X`
are conditionally independent, given the factual `Z`, of the whole response of `Y`: the map
sending each treatment value `a` to the potential response `Y_a`. The treatment set `X` is
arbitrary; its members may be descendants of one another. The value `x` is only used as a base
point. -/
theorem condIndepFun_response_of_backDoor [∀ v, Fintype (α v)] {X Y Z : Finset V}
    (hbd : G.BackDoor ↑X ↑Y ↑Z) (x : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => X.restrict (M.solve u))
      (fun u (a : ∀ v, α v) => Y.restrict ((M.intervene X a).solve u))
      (fun u => Z.restrict (M.solve u)) := by
  classical
  have h := M.condIndepFun_family_of_dSep X (κ := ∀ v, α v) id hbd.2
  have hXY := disjoint_left_of_backDoor (G := G) hbd
  -- the conditioning side: every world value of `Z` is the factual value
  have hZw : ∀ u (v : Z) (a : ∀ v, α v), M.world X a u v = M.solve u v := fun u v a =>
    M.world_of_notMem_descendantsOf a u (notMem_descendantsOf_erase_of_backDoor hbd v.2 v)
  have h1 := h.of_cond (Z' := fun u => Z.restrict (M.solve u)) (fun c v _ => c v)
    (fun s v => s v x) (fun u => funext fun v => funext fun a => hZw u v a)
    (fun u => funext fun v => (hZw u v x).symm)
  -- the right side: the world values of `Y` are the potential responses
  have h2 := h1.of_right (Y' := fun u (a : ∀ v, α v) => Y.restrict ((M.intervene X a).solve u))
    (fun s a v => s v a) (fun u => funext fun a => funext fun v =>
      (M.world_of_notMem a u (disjoint_right.1 hXY v.2)).symm)
  -- the left side: the factual treatments are a function of the world treatments
  refine h2.of_left (fun s => if hs : ∃ a : ∀ v, α v, ∀ v : X, s v a = a v then
      X.restrict (Classical.choose hs) else X.restrict x) (fun u => ?_)
  have hs : ∃ a : ∀ v, α v, ∀ v : X, M.world X (id a) u v = a v :=
    ⟨M.solve u, fun v => ((M.world_agree_iff X (M.solve u) u).2 fun _ _ => rfl) v v.2⟩
  simp only [id] at hs ⊢
  rw [dite_eq_left_of_eq_true (eq_true hs)]
  funext v
  exact ((M.world_agree_iff X _ u).1 fun w hw => Classical.choose_spec hs ⟨w, hw⟩) v v.2

/-- **Joint conditional ignorability from the back-door criterion.** If `Z` satisfies the
back-door criterion relative to `(X, Y)`, then for every finite family of treatment values
`(x_k)_k`, the family of potential responses `(Y_{x_k})_k`, all computed at one noise value, is
conditionally independent of the factual `X` given the factual `Z`, under the noise law. -/
theorem condIndepFun_family_of_backDoor {κ : Type*} [Fintype κ]
    {X Y Z : Finset V} (hbd : G.BackDoor ↑X ↑Y ↑Z) (x : κ → ∀ v, α v) (x₀ : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => X.restrict (M.solve u))
      (fun u k => Y.restrict ((M.intervene X (x k)).solve u))
      (fun u => Z.restrict (M.solve u)) :=
  have : ∀ v, Fintype (α v) := fun _ => Fintype.ofFinite _
  (M.condIndepFun_response_of_backDoor hbd x₀).of_right (fun r k => r (x k)) fun _ => rfl

/-- **Conditional ignorability from the back-door criterion** (Pearl 2009, section 11.3.2): if
`Z` satisfies the back-door criterion relative to `(X, Y)`, then for every treatment value `x`
the potential response `Y_x` is conditionally independent of the factual treatment `X` given
the factual `Z`, under the noise law: `Y_x ⫫ X | Z`. -/
theorem condIndepFun_potentialResponse_of_backDoor {X Y Z : Finset V}
    (hbd : G.BackDoor ↑X ↑Y ↑Z) (x : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => X.restrict (M.solve u))
      (fun u => Y.restrict ((M.intervene X x).solve u)) (fun u => Z.restrict (M.solve u)) :=
  have : ∀ v, Fintype (α v) := fun _ => Fintype.ofFinite _
  (M.condIndepFun_response_of_backDoor hbd x).of_right (fun r => r x) fun _ => rfl

/-- **Joint conditional ignorability for two treatment values**: if `Z` satisfies the back-door
criterion relative to `(X, Y)`, then `(Y_x, Y_x') ⫫ X | Z` under the noise law, with `X` and
`Z` factual. -/
theorem condIndepFun_potentialResponse_pair_of_backDoor {X Y Z : Finset V}
    (hbd : G.BackDoor ↑X ↑Y ↑Z) (x x' : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => X.restrict (M.solve u))
      (fun u => (Y.restrict ((M.intervene X x).solve u), Y.restrict ((M.intervene X x').solve u)))
      (fun u => Z.restrict (M.solve u)) :=
  have : ∀ v, Fintype (α v) := fun _ => Fintype.ofFinite _
  (M.condIndepFun_response_of_backDoor hbd x).of_right (fun r => (r x, r x')) fun _ => rfl

/-- **Conditional ignorability for one treatment vertex**: if `Z` satisfies the back-door
criterion relative to `({i}, Y)`, then `Y_x ⫫ X_i | Z` under the noise law, with the treatment
`X_i` and `Z` factual. For `Z` the parents of `i` this is the content of
`SCM.condIndepFun_intervene_singleton_parents` restricted to `Y`. -/
theorem condIndepFun_potentialResponse_of_backDoor_singleton {i : V} {Y Z : Finset V}
    (hbd : G.BackDoor {i} ↑Y ↑Z) (x : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => M.solve u i)
      (fun u => Y.restrict ((M.intervene {i} x).solve u)) (fun u => Z.restrict (M.solve u)) := by
  have hbd' : G.BackDoor ↑({i} : Finset V) ↑Y ↑Z := by rwa [coe_singleton]
  exact (M.condIndepFun_potentialResponse_of_backDoor hbd' x).of_left
    (fun s => s ⟨i, mem_singleton_self i⟩) fun _ => rfl

/-- **Joint conditional ignorability for one treatment vertex and two values**:
`(Y_x, Y_x') ⫫ X_i | Z` when `Z` satisfies the back-door criterion relative to `({i}, Y)`. -/
theorem condIndepFun_potentialResponse_pair_of_backDoor_singleton {i : V} {Y Z : Finset V}
    (hbd : G.BackDoor {i} ↑Y ↑Z) (x x' : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => M.solve u i)
      (fun u => (Y.restrict ((M.intervene {i} x).solve u),
        Y.restrict ((M.intervene {i} x').solve u))) (fun u => Z.restrict (M.solve u)) := by
  have hbd' : G.BackDoor ↑({i} : Finset V) ↑Y ↑Z := by rwa [coe_singleton]
  exact (M.condIndepFun_potentialResponse_pair_of_backDoor hbd' x x').of_left
    (fun s => s ⟨i, mem_singleton_self i⟩) fun _ => rfl

/-- **Single-world ignorability from the back-door criterion**: if `Z` satisfies the back-door
criterion relative to `(X, Y)`, then in the world of `do(X := x)` the potential response `Y_x`
is conditionally independent of the world treatments given the factual `Z`. The world value of
a treatment `v ∈ X` is its natural value under the intervention on the other treatments; this is
the statement read off the single world intervention graph. -/
theorem condIndepFun_world_of_backDoor {X Y Z : Finset V} (hbd : G.BackDoor ↑X ↑Y ↑Z)
    (x : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => X.restrict (M.world X x u))
      (fun u => Y.restrict ((M.intervene X x).solve u)) (fun u => Z.restrict (M.solve u)) := by
  have hXY := disjoint_left_of_backDoor (G := G) hbd
  have h := M.condIndepFun_world_of_dSep X x hbd.2
  have eY : (fun u => Y.restrict (M.world X x u)) =
      fun u => Y.restrict ((M.intervene X x).solve u) :=
    funext fun u => funext fun v => M.world_of_notMem x u (disjoint_right.1 hXY v.2)
  have eZ : (fun u => Z.restrict (M.world X x u)) = fun u => Z.restrict (M.solve u) :=
    funext fun u => funext fun v =>
      M.world_of_notMem_descendantsOf x u (notMem_descendantsOf_erase_of_backDoor hbd v.2 v)
  rwa [eY, eZ] at h

end Finite

/-! ### The adjustment formula from ignorability and consistency -/

section Fintype

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

/-- **Factorization of the world**: the law of the world of `do(A := x)` under the noise law
factorizes according to `G.deleteOutgoing A`, the graph of the random vertices of the single
world intervention graph. -/
theorem factorizes_world (A : Finset V) (x : ∀ v, α v) :
    (G.deleteOutgoing ↑A).Factorizes (M.noiseDist.map (M.world A x)) := by
  have h := (M.worldModel A x).factorizes
  rwa [SCM.dist, noiseDist_worldModel,
    show (M.worldModel A x).solve = M.world A x from funext (M.worldModel_solve A x)] at h


/-- **The factors of the world**: the mass of a world configuration `y` is the product, over
all vertices `v`, of the original kernel of `v` at the parent values of `y`, with the parents
in `A` held at their assigned values `x`. This is the factorization of the world distribution
of Richardson and Robins (2013): each world variable has the conditional law of its original
counterpart given the original parents, with the fixed nodes as parameters. -/
theorem map_world_apply_eq_prod (A : Finset V) (x y : ∀ v, α v) :
    (M.noiseDist.map (M.world A x)) y =
      ∏ v, M.kernel v (fun p => if p.1 ∈ A then x p.1 else y p.1) (y v) := by
  have h := (M.worldModel A x).dist_eq_prod y
  rw [SCM.dist, noiseDist_worldModel,
    show (M.worldModel A x).solve = M.world A x from funext (M.worldModel_solve A x)] at h
  rw [h]
  rfl

/-- **The back-door stratum identity from ignorability and consistency**: if `Z` satisfies the
back-door criterion relative to `(X, Y)`, then at every configuration `c`,
`P(y, z | do(x)) * P(x, z) = P(y, x, z) * P(z)`, all values read off `c`. This is the statement
of `SCM.backdoor_stratum`, proved here without the rules of the do-calculus: from
`Y_x ⫫ X | Z` (`SCM.condIndepFun_potentialResponse_of_backDoor`), consistency
(`Y_x = Y` where `X = x`) and the invariance of the nondescendants `Z`. -/
theorem backdoor_stratum_cf {X Y Z : Finset V} (hbd : G.BackDoor ↑X ↑Y ↑Z) (c : ∀ u, α u) :
    (M.intervene X c).dist.margAt (Y ∪ Z) c * M.dist.margAt (X ∪ Z) c =
      M.dist.margAt (Y ∪ X ∪ Z) c * M.dist.margAt Z c := by
  have h := M.condIndepFun_potentialResponse_of_backDoor hbd c (X.restrict c) (Y.restrict c)
    (Z.restrict c)
  simp only [FiniteDist.restrict_eq_restrict_iff] at h
  have hZ : ∀ u, ∀ v ∈ Z, (M.intervene X c).solve u v = M.solve u v := fun u v hv =>
    M.solve_intervene_of_notMem_descendantsOf u fun h' => hbd.1 v (mem_coe.2 hv) h'
  have e1 : M.noiseDist.probOf (fun u => (∀ v ∈ X, M.solve u v = c v) ∧
      (∀ v ∈ Y, (M.intervene X c).solve u v = c v) ∧ ∀ v ∈ Z, M.solve u v = c v) =
      M.dist.margAt (Y ∪ X ∪ Z) c := by
    rw [margAt_dist]
    refine FiniteDist.probOf_congr _ fun u => ?_
    simp only [forall_mem_union]
    constructor
    · rintro ⟨hx, hy, hz⟩
      rw [M.solve_intervene_of_agree hx] at hy
      exact ⟨⟨hy, hx⟩, hz⟩
    · rintro ⟨⟨hy, hx⟩, hz⟩
      rw [← M.solve_intervene_of_agree hx] at hy
      exact ⟨hx, hy, hz⟩
  have e2 : M.noiseDist.probOf (fun u => (∀ v ∈ Y, (M.intervene X c).solve u v = c v) ∧
      ∀ v ∈ Z, M.solve u v = c v) = (M.intervene X c).dist.margAt (Y ∪ Z) c := by
    rw [margAt_dist, noiseDist_intervene]
    refine FiniteDist.probOf_congr _ fun u => ?_
    simp only [forall_mem_union]
    exact and_congr Iff.rfl (forall₂_congr fun v hv => by rw [hZ u v hv])
  have e3 : M.noiseDist.probOf (fun u => (∀ v ∈ X, M.solve u v = c v) ∧
      ∀ v ∈ Z, M.solve u v = c v) = M.dist.margAt (X ∪ Z) c := by
    rw [margAt_dist]
    exact FiniteDist.probOf_congr _ fun u => by simp only [forall_mem_union]
  rw [e1, e2, e3, ← margAt_dist] at h
  rw [mul_comm, h]

/-- **Back-door adjustment from ignorability and consistency** (Pearl 2009, Theorem 3.3.2,
equation (3.19)): the statement of `SCM.effect_eq_sum_of_backDoor`, proved through the
counterfactual stratum identity `SCM.backdoor_stratum_cf` instead of the rules of the
do-calculus. If `Z` satisfies the back-door criterion relative to `(X, Y)`, `Y` is disjoint from
`Z`, and `P(z) > 0 → P(x, z) > 0`, then `P(y | do(x)) = ∑_z P(y | x, z) P(z)`. -/
theorem effect_eq_sum_of_backDoor_cf {X Y Z : Finset V} (v : ∀ u, α u)
    (hbd : G.BackDoor ↑X ↑Y ↑Z) (hYZ : Disjoint Y Z)
    (hpos : ∀ c : ∀ u, α u, (∀ u ∈ X, c u = v u) → 0 < M.dist.margAt Z c →
      0 < M.dist.margAt (X ∪ Z) c) :
    M.effect X v Y v = ∑ c ∈ FiniteDist.agreeOn Zᶜ v,
      M.dist.margAt (Y ∪ X ∪ Z) c / M.dist.margAt (X ∪ Z) c * M.dist.margAt Z c := by
  have hXZ := disjoint_of_backDoor (G := G) hbd
  rw [effect, FiniteDist.margAt_eq_sum_margAt _ (subset_union_left (s₂ := Z)),
    union_sdiff_cancel_left hYZ]
  refine sum_congr rfl fun c hc => ?_
  have hcX : ∀ u ∈ X, v u = c u := fun u hu =>
    ((FiniteDist.mem_agreeOn.1 hc) u (mem_compl.2 (disjoint_left.1 hXZ hu))).symm
  rw [M.intervene_congr hcX]
  have h2 := M.backdoor_stratum_cf hbd c
  have hZ : (M.intervene X c).dist.margAt Z c = M.dist.margAt Z c :=
    M.margAt_intervene_of_notMem_descendantsOf (fun u hu => hbd.1 u (mem_coe.2 hu)) c
  rcases (M.dist.margAt_nonneg Z c).eq_or_lt with h0 | hz
  · rw [← h0, mul_zero]
    refine le_antisymm ?_ (FiniteDist.margAt_nonneg _ _ _)
    rw [h0, ← hZ]
    exact FiniteDist.margAt_anti _ subset_union_right c
  · have hxz := hpos c (fun u hu => (hcX u hu).symm) hz
    field_simp
    linear_combination h2

/-- **The two routes to back-door adjustment agree.** Under the hypotheses of the back-door
adjustment formula, the counterfactual probability `P(Y_x = y)` of the noise law equals the
adjustment sum `∑_z P(y | x, z) P(z)` by the counterfactual route (ignorability and consistency,
`SCM.effect_eq_sum_of_backDoor_cf`), and the interventional probability `P(y | do(x))` equals the
same sum by the route through the rules of the do-calculus (`SCM.effect_eq_sum_of_backDoor`). -/
theorem effect_eq_sum_of_backDoor_routes_agree {X Y Z : Finset V} (v : ∀ u, α u)
    (hbd : G.BackDoor ↑X ↑Y ↑Z) (hYZ : Disjoint Y Z)
    (hpos : ∀ c : ∀ u, α u, (∀ u ∈ X, c u = v u) → 0 < M.dist.margAt Z c →
      0 < M.dist.margAt (X ∪ Z) c) :
    M.noiseDist.probOf (fun u => ∀ w ∈ Y, M.potentialResponse X v u w = v w) =
        ∑ c ∈ FiniteDist.agreeOn Zᶜ v,
          M.dist.margAt (Y ∪ X ∪ Z) c / M.dist.margAt (X ∪ Z) c * M.dist.margAt Z c ∧
      M.effect X v Y v = ∑ c ∈ FiniteDist.agreeOn Zᶜ v,
          M.dist.margAt (Y ∪ X ∪ Z) c / M.dist.margAt (X ∪ Z) c * M.dist.margAt Z c := by
  refine ⟨?_, M.effect_eq_sum_of_backDoor v hbd hYZ hpos⟩
  rw [← M.effect_eq_sum_of_backDoor_cf v hbd hYZ hpos, effect, margAt_dist]
  rfl

end Fintype

end SCM

end CausalInference
