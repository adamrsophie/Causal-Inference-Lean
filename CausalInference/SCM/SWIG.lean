/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.TwinBackDoor

/-!
# Single world intervention graphs

The single world intervention graph (SWIG) of Richardson and Robins (2013) represents the
world of an intervention `do(A := a)`: every treatment `a ∈ A` is split into a random half,
which keeps the edges into the treatment and carries its natural value, and a fixed half, the
constant `a`, which keeps the edges out of the treatment. Every other vertex `v` carries its
potential response `V_a`. Hernán and Robins, *Causal Inference: What If*, describe the
construction in section 7.5 (single treatment) and section 19.5 (two time points, where the
random half of the second treatment carries the natural value under the intervention on the
first one), and Fine Point 19.2 states the convention for the fixed nodes: every path through
a fixed node is blocked.

## Main definitions

* `Digraph.swigGraph G A`: the node-splitting transformation, a graph on `V ⊕ A`. The vertex
  `Sum.inl v` is the random half of `v` (the only half when `v ∉ A`), `Sum.inr a` the fixed
  half of the treatment `a`.
* `Digraph.SWIGSep G A S T C`: `S` and `T` are d-separated by `C` in the SWIG, with all fixed
  nodes added to the conditioning set, as the convention of Fine Point 19.2 prescribes.
* `SCM.swigConfig M A a u`: the configuration of the SWIG at the noise value `u`: the world
  values `SCM.world` on the random halves and the constants on the fixed halves.

## Main results

* `Digraph.swigGraph_isAcyclic`: node splitting preserves acyclicity; `DecidableRel` instances
  make small examples run by `decide`.
* `SCM.world_singleton_self`, `SCM.world_of_notMem`, `SCM.world_of_notMem_descendantsOf`
  (the last two in `CausalInference.SCM.TwinBackDoor`): the identification of the world
  variables. For a single treatment the random half is the factual treatment; outside `A` the
  world value is the potential response; a vertex that does not descend from the other
  treatments keeps its factual value (consistency for nondescendants).
* `Digraph.swigSep_iff`: d-separation in the SWIG with the fixed nodes conditioned on is
  d-separation in `G.deleteOutgoing A`, the graph of the random halves.
* `SCM.factorizes_world`, `SCM.map_world_apply_eq_prod` (in `TwinBackDoor`): the law of the
  random halves factorizes according to the SWIG with the fixed nodes removed, each factor
  being the original kernel with the fixed parents held at their constants.
* `SCM.condIndepFun_world_of_swigSep` (**the SWIG Markov property**, Richardson and Robins
  2013): d-separation in the SWIG implies the corresponding conditional independence of the
  world variables under the noise law.
* `Digraph.swigSep_singleton_iff_backDoor`: for a single treatment and a set `L` of
  nondescendants, `Y_a` and `A` are d-separated by `L` in the SWIG exactly when `L` satisfies
  the back-door criterion (What If, section 7.5). `SCM.condIndepFun_of_swigSep_singleton`
  reads conditional exchangeability `Y_a ⫫ A | L` off the SWIG; it has the conclusion of
  `SCM.condIndepFun_potentialResponse_of_backDoor_singleton`.

The examples (longitudinal treatments, a failure of conditional exchangeability, and the
comparison with the twin network) are in `CausalInference.SCM.SWIGExamples`.

## References

* T. S. Richardson and J. M. Robins (2013), *Single World Intervention Graphs (SWIGs): A
  Unification of the Counterfactual and Graphical Approaches to Causality*.
* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, section 7.5, Fine Point 7.4,
  section 19.5, Fine Point 19.2 and Technical Point 19.3.
-/

@[expose] public section

namespace Digraph

open Finset Relation

variable {V : Type*}

/-! ### The node-splitting transformation -/

/-- The single world intervention graph of `G` for the intervention set `A`, on `V ⊕ A`. The
vertex `Sum.inl v` is the random half of `v`: for `v ∈ A` it keeps the edges into `v` and loses
the edges out of `v`; for `v ∉ A` it is the vertex `v` itself. The vertex `Sum.inr a` is the
fixed half of the treatment `a`: it has no edge into it and keeps the edges out of `a`. -/
def swigGraph (G : Digraph V) (A : Finset V) : Digraph (V ⊕ A) where
  Adj s t := match s, t with
    | .inl u, .inl v => G.Adj u v ∧ u ∉ A
    | .inr a, .inl v => G.Adj a.1 v
    | _, _ => False

variable {G : Digraph V} {A : Finset V}

theorem swigGraph_adj_inl_inl {u v : V} :
    (G.swigGraph A).Adj (.inl u) (.inl v) ↔ G.Adj u v ∧ u ∉ A := Iff.rfl

theorem swigGraph_adj_inr_inl {a : A} {v : V} :
    (G.swigGraph A).Adj (.inr a) (.inl v) ↔ G.Adj a.1 v := Iff.rfl

/-- A fixed node has no parent. -/
theorem swigGraph_not_adj_inr (s : V ⊕ A) (a : A) : ¬ (G.swigGraph A).Adj s (.inr a) := by
  rcases s with s | s <;> exact id

/-- Between random halves, the SWIG has the edges of `G.deleteOutgoing A`. -/
theorem swigGraph_adj_inl_inl_iff {u v : V} :
    (G.swigGraph A).Adj (.inl u) (.inl v) ↔ (G.deleteOutgoing ↑A).Adj u v := Iff.rfl

instance [DecidableEq V] [DecidableRel G.Adj] : DecidableRel (G.swigGraph A).Adj := fun s t =>
  match s, t with
  | .inl u, .inl v => inferInstanceAs (Decidable (G.Adj u v ∧ u ∉ A))
  | .inr a, .inl v => inferInstanceAs (Decidable (G.Adj a.1 v))
  | .inl _, .inr _ => inferInstanceAs (Decidable False)
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

/-- **Node splitting preserves acyclicity**: a topological order of `G`, shifted by one on the
random halves, with the fixed halves at the bottom, is a topological order of the SWIG. -/
theorem swigGraph_isAcyclic [Finite V] (hG : G.IsAcyclic) (A : Finset V) :
    (G.swigGraph A).IsAcyclic := by
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  refine isAcyclic_of_adj_lt (fun t => Sum.elim (fun v => f v + 1) (fun _ => 0) t) ?_
  rintro (a | a) (b | b) h <;> simp_all [swigGraph]

/-! ### d-separation in the SWIG -/

/-- The conditioning set of the SWIG for the set `C` of random halves: the random halves of `C`
together with all fixed nodes. -/
def swigCond (C : Set V) (A : Finset V) : Set (V ⊕ A) := Sum.inl '' C ∪ Set.range Sum.inr

theorem inl_notMem_swigCond {C : Set V} {v : V} (hv : v ∉ C) :
    (Sum.inl v : V ⊕ A) ∉ swigCond C A := by
  rintro (⟨c, hc, he⟩ | ⟨a, ha⟩)
  · exact hv (Sum.inl_injective he ▸ hc)
  · exact Sum.inr_ne_inl ha

theorem inl_mem_swigCond_iff {C : Set V} {v : V} :
    (Sum.inl v : V ⊕ A) ∈ swigCond C A ↔ v ∈ C := by
  refine ⟨fun h => ?_, fun h => Or.inl ⟨v, h, rfl⟩⟩
  by_contra hv
  exact inl_notMem_swigCond hv h

theorem inr_mem_swigCond {C : Set V} (a : A) : (Sum.inr a : V ⊕ A) ∈ swigCond C A :=
  Or.inr ⟨a, rfl⟩

/-- A directed path of the SWIG from a random half stays among the random halves and is a
directed path of `G.deleteOutgoing A`. -/
theorem exists_of_reflTransGen_swigGraph {v : V} {t : V ⊕ A}
    (h : ReflTransGen (G.swigGraph A).Adj (.inl v) t) :
    ∃ w, t = .inl w ∧ ReflTransGen (G.deleteOutgoing ↑A).Adj v w := by
  induction h with
  | refl => exact ⟨v, rfl, ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨w, rfl, hw⟩ := ih
    rcases c with c | c
    · exact ⟨c, rfl, hw.tail hbc⟩
    · exact absurd hbc (swigGraph_not_adj_inr _ c)

/-- The random half of `v` is an ancestor of the SWIG conditioning set exactly when `v` is an
ancestor of `C` in `G.deleteOutgoing A`. -/
theorem inl_mem_ancestorsOf_swigCond_iff {C : Set V} {v : V} :
    (Sum.inl v : V ⊕ A) ∈ (G.swigGraph A).ancestorsOf (swigCond C A) ↔
      v ∈ (G.deleteOutgoing ↑A).ancestorsOf C := by
  constructor
  · rintro ⟨s, hs, hvs⟩
    obtain ⟨w, rfl, hw⟩ := exists_of_reflTransGen_swigGraph hvs
    exact ⟨w, inl_mem_swigCond_iff.1 hs, hw⟩
  · rintro ⟨w, hw, hvw⟩
    exact ⟨.inl w, inl_mem_swigCond_iff.2 hw, hvw.lift Sum.inl fun _ _ h => h⟩

/-- A step of the Bayes-ball state graph of `G.deleteOutgoing A` lifts to the SWIG. -/
theorem swig_bayesBall_adj_iff {C : Set V} {v w : V} {b c : Bool} :
    ((G.swigGraph A).bayesBall (swigCond C A)).Adj (.inl v, b) (.inl w, c) ↔
      ((G.deleteOutgoing ↑A).bayesBall C).Adj (v, b) (w, c) := by
  unfold bayesBall Passes
  simp only [inl_mem_ancestorsOf_swigCond_iff, inl_mem_swigCond_iff]
  rfl

/-- A path of the Bayes-ball state graph of the SWIG that starts at a random half, entered
without an arrowhead, either stays among the random halves, where it is a path of the state
graph of `G.deleteOutgoing A`, or ends at a fixed node, entered without an arrowhead. -/
theorem swig_bayesBall_reflTransGen {C : Set V} {x : V} {t : (V ⊕ A) × Bool}
    (h : ReflTransGen ((G.swigGraph A).bayesBall (swigCond C A)).Adj (.inl x, false) t) :
    (∃ w, t.1 = .inl w ∧ ReflTransGen ((G.deleteOutgoing ↑A).bayesBall C).Adj (x, false)
      (w, t.2)) ∨ ∃ a, t.1 = .inr a ∧ t.2 = false := by
  induction h with
  | refl => exact Or.inl ⟨x, rfl, ReflTransGen.refl⟩
  | @tail s t _ hst ih =>
    rcases ih with ⟨w, hw, hpath⟩ | ⟨a, ha, hs2⟩
    · obtain ⟨s1, s2⟩ := s
      obtain ⟨t1, t2⟩ := t
      simp only at hw
      subst hw
      rcases t1 with t1 | t1
      · exact Or.inl ⟨t1, rfl, hpath.tail (swig_bayesBall_adj_iff.1 hst)⟩
      · refine Or.inr ⟨t1, rfl, ?_⟩
        cases t2
        · rfl
        · exact absurd (bayesBall_adj_true.1 hst).1 (swigGraph_not_adj_inr _ t1)
    · obtain ⟨s1, s2⟩ := s
      obtain ⟨t1, t2⟩ := t
      simp only at ha hs2
      subst ha hs2
      exact absurd (inr_mem_swigCond a) (notMem_of_bayesBall_adj_false hst)

/-- **d-separation in the SWIG.** With all fixed nodes added to the conditioning set, the random
halves of `S` and `T` are d-separated by those of `C` in the SWIG exactly when `S` and `T` are
d-separated by `C` in `G.deleteOutgoing A`, the graph of the random halves. A trail through a
fixed node passes it as a non-collider (a fixed node has no parent), so conditioning on the
fixed nodes blocks every such trail. -/
theorem dSep_swigGraph_iff {S T C : Set V} :
    (G.swigGraph A).DSep (Sum.inl '' S) (Sum.inl '' T) (swigCond C A) ↔
      (G.deleteOutgoing ↑A).DSep S T C := by
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxC, hyC, b, hxy⟩
    rcases swig_bayesBall_reflTransGen hxy with ⟨w, hw, hpath⟩ | ⟨a, ha, -⟩
    · cases Sum.inl_injective hw
      exact ⟨x, hx, y, hy, fun h => hxC (Or.inl ⟨x, h, rfl⟩), fun h => hyC (Or.inl ⟨y, h, rfl⟩),
        b, hpath⟩
    · exact absurd ha Sum.inl_ne_inr
  · rintro ⟨x, hx, y, hy, hxC, hyC, b, hxy⟩
    exact ⟨.inl x, ⟨x, hx, rfl⟩, .inl y, ⟨y, hy, rfl⟩, inl_notMem_swigCond hxC,
      inl_notMem_swigCond hyC, b, hxy.lift (fun s : V × Bool => ((Sum.inl s.1 : V ⊕ A), s.2))
        fun _ _ h => swig_bayesBall_adj_iff.2 h⟩

variable [DecidableEq V]

/-- `G.SWIGSep A S T C`: in the single world intervention graph of `G` for `A`, the random
halves of `S` and `T` are d-separated by the random halves of `C` together with all fixed
nodes. Following Hernán and Robins (What If, Fine Point 19.2), every path through a fixed node
is blocked, so the fixed nodes are conditioned on. The sets are finite so that the relation is
decidable. -/
def SWIGSep (G : Digraph V) (A S T C : Finset V) : Prop :=
  (G.swigGraph A).DSep ↑(S.image (Sum.inl : V → V ⊕ A)) ↑(T.image (Sum.inl : V → V ⊕ A))
    ↑(C.image (Sum.inl : V → V ⊕ A) ∪ (univ : Finset A).image Sum.inr)

instance [Fintype V] [DecidableRel G.Adj] (S T C : Finset V) :
    Decidable (G.SWIGSep A S T C) := by
  unfold SWIGSep
  infer_instance

/-- **The SWIG separation is d-separation in the graph of the random halves**:
`G.SWIGSep A S T C` holds exactly when `S` and `T` are d-separated by `C` in
`G.deleteOutgoing A`. -/
theorem swigSep_iff {S T C : Finset V} :
    G.SWIGSep A S T C ↔ (G.deleteOutgoing ↑A).DSep ↑S ↑T ↑C := by
  have hC : (↑(C.image Sum.inl ∪ (univ : Finset A).image Sum.inr) : Set (V ⊕ A)) =
      swigCond ↑C A := by
    ext t
    simp [swigCond]
  unfold SWIGSep
  rw [coe_image, coe_image, hC]
  exact dSep_swigGraph_iff

/-- **The SWIG reading of the back-door criterion** (What If, section 7.5: "`Y^a` is
d-separated from `A` given `L` if and only if `L` is a non-descendant of `A` that blocks all
backdoor paths from `A` to `Y`"). For a single treatment `i` and a set `L` of vertices that are
not descendants of `i`, the random half of `i` and the potential outcomes `Y` are d-separated
by `L` in the SWIG of `do(i)` exactly when `L` satisfies the back-door criterion relative to
`({i}, Y)`. -/
theorem swigSep_singleton_iff_backDoor {i : V} {Y L : Finset V}
    (hL : ∀ l ∈ L, l ∉ G.descendantsOf {i}) :
    G.SWIGSep {i} {i} Y L ↔ G.BackDoor {i} ↑Y ↑L := by
  rw [swigSep_iff, coe_singleton]
  exact ⟨fun h => ⟨fun l hl => hL l (mem_coe.1 hl), h⟩, fun h => h.2⟩

end Digraph

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-! ### The variables of the SWIG -/

/-- For a single treatment, the random half carries the factual treatment: the world value of
`i` in the world of `do(i := x)` is its value without intervention. -/
theorem world_singleton_self (i : V) (x : ∀ v, α v) (u : ∀ v, ε v) :
    M.world {i} x u i = M.solve u i := by
  rw [world_apply, erase_singleton, solve_intervene_empty]

/-- The value types of the SWIG: `α v` at the random half of `v`, and `α a` at the fixed half of
the treatment `a`. -/
abbrev swigVal (α : V → Type*) (A : Finset V) : V ⊕ A → Type _ :=
  Sum.elim α fun a => α a.1

/-- The configuration of the SWIG of `do(A := x)` at the noise value `u`: the world value
`SCM.world` at every random half, and the constant `x a` at the fixed half of `a`. -/
noncomputable def swigConfig (A : Finset V) (x : ∀ v, α v) (u : ∀ v, ε v) :
    ∀ t, swigVal α A t
  | .inl v => M.world A x u v
  | .inr a => x a.1

@[simp] theorem swigConfig_inl (A : Finset V) (x : ∀ v, α v) (u : ∀ v, ε v) (v : V) :
    M.swigConfig A x u (.inl v) = M.world A x u v := rfl

/-- The fixed half of a treatment carries the constant assigned to it, at every noise value. -/
@[simp] theorem swigConfig_inr (A : Finset V) (x : ∀ v, α v) (u : ∀ v, ε v) (a : A) :
    M.swigConfig A x u (.inr a) = x a.1 := rfl

/-- The value of a treatment in the world of `do(A := x)` is the constant of its fixed half: the
random half of a child `v ∉ A` reads it through the structural equation of `v`
(`SCM.world_eq`), and the treatment itself takes it under the intervention. -/
theorem solve_intervene_eq_swigConfig_inr (A : Finset V) (x : ∀ v, α v) (u : ∀ v, ε v)
    (a : A) : (M.intervene A x).solve u a.1 = M.swigConfig A x u (.inr a) :=
  M.solve_intervene_of_mem u a.2

/-! ### The Markov property of the SWIG -/

/-- **The SWIG Markov property** (Richardson and Robins 2013): if the random halves of `S` and
`T` are d-separated in the SWIG of `do(A := x)` by the random halves of `C` together with the
fixed nodes, then under the noise law the world variables of `S` and of `T` are conditionally
independent given those of `C`. -/
theorem condIndepFun_world_of_swigSep [∀ v, Finite (α v)] [∀ v, DecidableEq (α v)]
    (A : Finset V) (x : ∀ v, α v) {S T C : Finset V} (h : G.SWIGSep A S T C) :
    M.noiseDist.CondIndepFun (fun u => S.restrict (M.world A x u))
      (fun u => T.restrict (M.world A x u)) (fun u => C.restrict (M.world A x u)) :=
  M.condIndepFun_world_of_dSep A x (Digraph.swigSep_iff.1 h)

/-- **Conditional exchangeability read off the SWIG** (What If, section 7.5): for a single
treatment `i` and a set `L` of nondescendants of `i`, if the random half of `i` and the outcomes
`Y` are d-separated by `L` in the SWIG, then `Y_x ⫫ X_i | L` under the noise law, with `X_i` and
`L` factual. The conclusion is that of `SCM.condIndepFun_potentialResponse_of_backDoor_singleton`
and the hypothesis is equivalent to its back-door hypothesis
(`Digraph.swigSep_singleton_iff_backDoor`); the proof here reads the independence off the world
model and identifies the world variables. -/
theorem condIndepFun_of_swigSep_singleton [∀ v, Finite (α v)] [∀ v, DecidableEq (α v)]
    {i : V} {Y L : Finset V} (hL : ∀ l ∈ L, l ∉ G.descendantsOf {i})
    (h : G.SWIGSep {i} {i} Y L) (x : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => M.solve u i)
      (fun u => Y.restrict ((M.intervene {i} x).solve u)) (fun u => L.restrict (M.solve u)) := by
  have hbd := (Digraph.swigSep_singleton_iff_backDoor hL).1 h
  have hiY : i ∉ Y := fun hi => disjoint_left.1 (disjoint_left_of_backDoor (G := G) (X := {i})
    (Y := Y) (Z := L) (by rwa [coe_singleton])) (mem_singleton_self i) hi
  have hw := M.condIndepFun_world_of_swigSep {i} x h
  have eY : (fun u => Y.restrict (M.world {i} x u)) =
      fun u => Y.restrict ((M.intervene {i} x).solve u) :=
    funext fun u => funext fun v => M.world_of_notMem x u fun hv =>
      hiY (mem_singleton.1 hv ▸ v.2)
  have eL : (fun u => L.restrict (M.world {i} x u)) = fun u => L.restrict (M.solve u) :=
    funext fun u => funext fun v => M.world_of_notMem_descendantsOf x u fun hv =>
      hL v v.2 (Digraph.descendantsOf_mono (by simp) hv)
  rw [eY, eL] at hw
  exact hw.of_left (fun s => s ⟨i, mem_singleton_self i⟩) fun u =>
    (M.world_singleton_self i x u).symm

end SCM

end CausalInference
