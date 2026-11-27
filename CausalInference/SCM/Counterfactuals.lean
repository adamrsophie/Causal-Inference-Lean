/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Intervention

/-!
# Unit-level counterfactuals in finite structural causal models

The potential response `Y_x(u)` of a vertex `Y` to the intervention `do(X := x)` at the noise
value `u` is the value of `Y` in the solution of the submodel of `do(X := x)` at `u`, that is
`(M.intervene X x).solve u Y` (Pearl 2009, Definition 7.1.4). Since the submodel keeps the noise
space, the factual and counterfactual worlds share the same `u`.

## Main definitions

* `SCM.potentialResponse M X x u` (defined in `CausalInference.SCM.Intervention`): the potential
  response `V_x(u)`, the solution of the submodel of `do(X := x)` at the noise value `u`.
* `SCM.counterfactualProb M E hE X x Q`: the probability of the counterfactual event `Q` under
  `do(X := x)` given the factual evidence `E`, computed by abduction (condition the noise law on
  `E`), action (pass to the submodel of `do(X := x)`), and prediction (push the conditioned noise
  law forward along the submodel's solution map) (Pearl 2009, Theorem 7.1.7).
* `SCM.cfFamilyDist M X x`, `SCM.jointCounterfactualProb M E hE X x Q`: the joint law of the
  potential responses `(V_{x k})_k` to a finite family of interventions at one shared noise
  draw, and the joint counterfactual probability given evidence.

## Main results

* `SCM.solve_intervene_of_agree` (**consistency**, Pearl 2009, Corollary 7.3.2): if
  `X(u) = x`, then `V_x(u) = V(u)` for every vertex.
* `SCM.solve_intervene_intervene_of_agree`, `SCM.solve_intervene_union_of_agree`
  (**composition**, Pearl 2009, Property 1): if `W_x(u) = w`, then `V_{xw}(u) = V_x(u)`.
* `SCM.solve_intervene_intervene_of_mem` (**effectiveness**, Pearl 2009, Property 2):
  `X_{xw}(u) = x` outside `W`.
* `SCM.solve_eq_of_reversibility` (**reversibility** for recursive models, Pearl 2009,
  Property 3 and the argument on p. 230): for distinct vertices `Y` and `W`, `Y_w(u) = y` and
  `W_y(u) = w` imply `Y(u) = y`. Applied to the submodel `M.intervene X x` this is
  `Y_{xw}(u) = y ∧ W_{xy}(u) = w → Y_x(u) = y`.
* `SCM.potentialResponse_of_agree`, `SCM.potentialResponse_union_of_agree`,
  `SCM.potentialResponse_of_mem`: consistency, composition and effectiveness stated with
  potential responses. `SCM.potentialResponse_eq_of_reversibility`: reversibility with a prior
  intervention, `Y_{xw}(u) = y ∧ W_{xy}(u) = w → Y_x(u) = y` (Pearl 2009, (7.21)).
* `SCM.counterfactualProb_eq`: the counterfactual probability given evidence is
  `P_u(E(V(u)) ∧ Q(V_x(u))) / P(E)`, Pearl's formula (7.6) with the noise posterior written out.
* `SCM.counterfactualProb_of_agree` (**consistency for probabilities**): evidence that fixes
  `X = x` makes `P(Q(V_x) | E)` the observational `P(Q | E)`.
* `SCM.probOf_cfFamilyDist`, `SCM.map_eval_cfFamilyDist`, `SCM.jointCounterfactualProb_eq`,
  `SCM.jointCounterfactualProb_eval`: joint counterfactual events across several interventions
  (Pearl 2009, (7.5)), and their marginals, the single-intervention laws. The joint law of the
  factual world and one counterfactual world is `SCM.cfJointDist` in
  `CausalInference.SCM.TwinNetwork`, a marginal of `cfFamilyDist`
  (`SCM.cfJointDist_eq_map_cfFamilyDist`).
* `SCMExamples.pearlModel1`, `SCMExamples.pearlModel2` (Pearl 2009, equations (1.47), (1.48)):
  two models on `X → Y` with the same observational distribution (`P(x, y) = 1/4`) and the same
  interventional distributions for every intervention, but with
  `P(Y_{X=0} = 0 | X = 1, Y = 1)` equal to `0` in the first and to `1` in the second.

Sources: Pearl (2009), *Causality*, 2nd edition, sections 1.4.4, 7.1 and 7.3.1; Galles and Pearl
(1997).
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-! ### The axioms of structural counterfactuals -/

/-- **Consistency** (Pearl 2009, Corollary 7.3.2, equation (7.20)): at a noise value `u` where
the vertices of `X` take the values `x` without intervention, the intervention `do(X := x)`
changes nothing: `V_x(u) = V(u)`. -/
theorem solve_intervene_of_agree {X : Finset V} {x : ∀ v, α v} {u : ∀ v, ε v}
    (h : ∀ v ∈ X, M.solve u v = x v) : (M.intervene X x).solve u = M.solve u :=
  ((M.intervene X x).eq_solve_of_isSolution
    (M.isSolution_intervene_iff.2 ⟨h, fun v _ => M.solve_eq u v⟩)).symm

/-- **Composition** (Pearl 2009, Property 1, equation (7.19)), for a later intervention: if the
vertices of `W` take the values `w` under `do(X := x)`, then additionally setting `W := w`
changes nothing: `V_{xw}(u) = V_x(u)`. -/
theorem solve_intervene_intervene_of_agree {X W : Finset V} {x w : ∀ v, α v} {u : ∀ v, ε v}
    (h : ∀ v ∈ W, (M.intervene X x).solve u v = w v) :
    ((M.intervene X x).intervene W w).solve u = (M.intervene X x).solve u :=
  (M.intervene X x).solve_intervene_of_agree h

/-- **Composition** (Pearl 2009, Property 1, equation (7.19)), for the simultaneous intervention
on `X ∪ W`: if `W_x(u) = w`, then `V_{xw}(u) = V_x(u)`. -/
theorem solve_intervene_union_of_agree {X W : Finset V} {x w : ∀ v, α v} {u : ∀ v, ε v}
    (h : ∀ v ∈ W, (M.intervene X x).solve u v = w v) :
    (M.intervene (X ∪ W) fun v => if v ∈ W then w v else x v).solve u =
      (M.intervene X x).solve u := by
  rw [← M.solve_intervene_intervene, M.solve_intervene_intervene_of_agree h]

/-- **Effectiveness** (Pearl 2009, Property 2): under `do(X := x)` followed by `do(W := w)`, a
vertex of `X` outside `W` takes the value `x`: `X_{xw}(u) = x`. -/
theorem solve_intervene_intervene_of_mem {X W : Finset V} {x w : ∀ v, α v} (u : ∀ v, ε v)
    {v : V} (hvX : v ∈ X) (hvW : v ∉ W) :
    ((M.intervene X x).intervene W w).solve u v = x v := by
  rw [M.solve_intervene_intervene, M.solve_intervene_of_mem u (mem_union_left W hvX)]
  simp [hvW]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- In a graph, a vertex `b ≠ a` that is not a strict descendant of `a` is not in the descendant
closure of `{a}`. -/
theorem notMem_descendantsOf_singleton {a b : V} (hne : a ≠ b) (h : ¬ G.IsAncestor a b) :
    b ∉ G.descendantsOf {a} := by
  intro hb
  obtain ⟨s, hs, hsb⟩ := Digraph.mem_descendantsOf.1 hb
  rw [Set.mem_singleton_iff] at hs
  subst hs
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hsb with h' | h'
  · exact hne h'.symm
  · exact h h'

/-- **Reversibility** for recursive models (Pearl 2009, Property 3, equation (7.21), and the
argument on p. 230): for distinct vertices `Y` and `W`, if setting `W := w` gives `Y` the value
`y Y`, and setting `Y := y` gives `W` the value `w W`, then `Y` has the value `y Y` without
intervention. Applied to the submodel `M.intervene X x` (itself a model), this is
`Y_{xw}(u) = y ∧ W_{xy}(u) = w → Y_x(u) = y`. -/
theorem solve_eq_of_reversibility {Y W : V} (hYW : Y ≠ W) (w y : ∀ v, α v) (u : ∀ v, ε v)
    (h1 : (M.intervene {W} w).solve u Y = y Y) (h2 : (M.intervene {Y} y).solve u W = w W) :
    M.solve u Y = y Y := by
  by_cases hWY : G.IsAncestor W Y
  · -- `Y` is a descendant of `W`, so `W` is not a descendant of `Y`
    have hW : W ∉ G.descendantsOf ↑({Y} : Finset V) := by
      rw [coe_singleton]
      exact notMem_descendantsOf_singleton hYW (M.acyclic.isAncestor_asymm hWY)
    rw [M.solve_intervene_of_notMem_descendantsOf u hW] at h2
    have hc := M.solve_intervene_of_agree (X := {W}) (x := w) (u := u)
      (fun v hv => by rw [mem_singleton.1 hv]; exact h2)
    rwa [hc] at h1
  · have hY : Y ∉ G.descendantsOf ↑({W} : Finset V) := by
      rw [coe_singleton]
      exact notMem_descendantsOf_singleton (Ne.symm hYW) hWY
    rwa [M.solve_intervene_of_notMem_descendantsOf u hY] at h1

/-! ### The axioms in terms of potential responses -/

/-- **The empty intervention**: `V_∅(u) = V(u)`. -/
theorem potentialResponse_empty (x : ∀ v, α v) (u : ∀ v, ε v) :
    M.potentialResponse ∅ x u = M.solve u := by
  rw [potentialResponse_eq, solve_intervene_empty]

/-- **Consistency** (Pearl 2009, Corollary 7.3.2, equation (7.20)), with potential responses:
if `X(u) = x`, then `V_x(u) = V(u)`. -/
theorem potentialResponse_of_agree {X : Finset V} {x : ∀ v, α v} {u : ∀ v, ε v}
    (h : ∀ v ∈ X, M.solve u v = x v) : M.potentialResponse X x u = M.solve u :=
  M.solve_intervene_of_agree h

/-- **Effectiveness** (Pearl 2009, Property 2), with potential responses: `X_x(u) = x`. -/
theorem potentialResponse_of_mem {X : Finset V} (x : ∀ v, α v) (u : ∀ v, ε v) {v : V}
    (hv : v ∈ X) : M.potentialResponse X x u v = x v :=
  M.solve_intervene_of_mem u hv

/-- **Composition** (Pearl 2009, Property 1, equation (7.19)), with potential responses: if
`W_x(u) = w`, then `V_{xw}(u) = V_x(u)`, where `xw` sets `W` to `w` and the rest of `X` to `x`. -/
theorem potentialResponse_union_of_agree {X W : Finset V} {x w : ∀ v, α v} {u : ∀ v, ε v}
    (h : ∀ v ∈ W, M.potentialResponse X x u v = w v) :
    M.potentialResponse (X ∪ W) (fun v => if v ∈ W then w v else x v) u =
      M.potentialResponse X x u :=
  M.solve_intervene_union_of_agree h

/-- **Reversibility** for recursive models (Pearl 2009, Property 3, equation (7.21)), with a
prior intervention `do(X := x)`: for distinct vertices `Y` and `W`,
`Y_{xw}(u) = y ∧ W_{xy}(u) = w → Y_x(u) = y`. Here `xw` sets `W` to `w` and the rest of `X` to
`x`, and `xy` sets `Y` to `y` and the rest of `X` to `x`. -/
theorem potentialResponse_eq_of_reversibility (X : Finset V) (x : ∀ v, α v) {Y W : V}
    (hYW : Y ≠ W) (w y : ∀ v, α v) (u : ∀ v, ε v)
    (h1 : M.potentialResponse (X ∪ {W}) (fun v => if v ∈ ({W} : Finset V) then w v else x v) u
      Y = y Y)
    (h2 : M.potentialResponse (X ∪ {Y}) (fun v => if v ∈ ({Y} : Finset V) then y v else x v) u
      W = w W) :
    M.potentialResponse X x u Y = y Y := by
  rw [potentialResponse_eq, ← solve_intervene_intervene] at h1 h2
  exact (M.intervene X x).solve_eq_of_reversibility hYW w y u h1 h2

/-! ### Abduction, action, prediction -/

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

/-- **Abduction, action, prediction** (Pearl 2009, Theorem 7.1.7): the probability of the
counterfactual event `Q` under `do(X := x)`, given the factual evidence `E` of positive
probability. Abduction conditions the noise law on the evidence `E(V(u))`; action passes to the
submodel of `do(X := x)`; prediction is the probability of `Q` under the pushforward of the
conditioned noise law along the submodel's solution map. -/
noncomputable def counterfactualProb (E : (∀ v, α v) → Prop) [DecidablePred E]
    (hE : 0 < M.dist.probOf E) (X : Finset V) (x : ∀ v, α v) (Q : (∀ v, α v) → Prop)
    [DecidablePred Q] : ℝ :=
  ((M.noiseDist.cond (fun u => E (M.solve u)) (by rwa [← probOf_dist])).map
    (M.intervene X x).solve).probOf Q

/-- The counterfactual probability given evidence, in closed form (Pearl 2009, equation (7.6)):
`P(Q(V_x) | E) = P_u(E(V(u)) ∧ Q(V_x(u))) / P(E)`. -/
theorem counterfactualProb_eq (E : (∀ v, α v) → Prop) [DecidablePred E]
    (hE : 0 < M.dist.probOf E) (X : Finset V) (x : ∀ v, α v) (Q : (∀ v, α v) → Prop)
    [DecidablePred Q] :
    M.counterfactualProb E hE X x Q =
      M.noiseDist.probOf (fun u => E (M.solve u) ∧ Q ((M.intervene X x).solve u)) /
        M.dist.probOf E := by
  rw [counterfactualProb, FiniteDist.probOf_map, FiniteDist.probOf_cond, probOf_dist]

/-- **Consistency for counterfactual probabilities**: if the evidence `E` already fixes the
vertices of `X` at the values `x`, the counterfactual `P(Q(V_x) | E)` is the ordinary
conditional probability `P(Q | E)` under the observational distribution. -/
theorem counterfactualProb_of_agree (E : (∀ v, α v) → Prop) [DecidablePred E]
    (hE : 0 < M.dist.probOf E) (X : Finset V) (x : ∀ v, α v) (Q : (∀ v, α v) → Prop)
    [DecidablePred Q] (hEX : ∀ y, E y → ∀ v ∈ X, y v = x v) :
    M.counterfactualProb E hE X x Q = (M.dist.cond E hE).probOf Q := by
  rw [counterfactualProb_eq, FiniteDist.probOf_cond, M.probOf_dist (fun y => E y ∧ Q y)]
  congr 1
  refine FiniteDist.probOf_congr _ fun u => and_congr_right fun hu => ?_
  rw [M.solve_intervene_of_agree (hEX _ hu)]

/-! ### Joint counterfactuals across several interventions -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The **joint law of the potential responses to a family of interventions** `do(X k := x k)`,
indexed by a finite type `κ`, all computed at one shared noise draw: the law of
`k ↦ V_{x k}(u)` when `u` has the noise law of `M`. The factual world is the index with
`X k = ∅` (`SCM.potentialResponse_empty`). -/
noncomputable def cfFamilyDist (X : κ → Finset V) (x : κ → ∀ v, α v) :
    FiniteDist (κ → ∀ v, α v) :=
  M.noiseDist.map fun u k => M.potentialResponse (X k) (x k) u

/-- Joint counterfactual events have the probability
`P(Q((V_{x k})_k)) = P_u(Q((V_{x k}(u))_k))`, with the same noise value `u` in every world
(Pearl 2009, equation (7.5)). -/
theorem probOf_cfFamilyDist (X : κ → Finset V) (x : κ → ∀ v, α v)
    (Q : (κ → ∀ v, α v) → Prop) [DecidablePred Q] :
    (M.cfFamilyDist X x).probOf Q =
      M.noiseDist.probOf (fun u => Q fun k => M.potentialResponse (X k) (x k) u) :=
  FiniteDist.probOf_map _ _ _

/-- The marginals of the joint law are the interventional distributions: the law of
`V_{x k}` alone is the distribution induced by `do(X k := x k)`. -/
theorem map_eval_cfFamilyDist (X : κ → Finset V) (x : κ → ∀ v, α v) (k : κ) :
    (M.cfFamilyDist X x).map (fun f => f k) = (M.intervene (X k) (x k)).dist := by
  rw [cfFamilyDist, FiniteDist.map_map]
  rfl

/-- The joint counterfactual probability of an event `Q` about the worlds `(V_{x k})_k`, given
factual evidence `E` of positive probability, by abduction, action and prediction with one
shared posterior noise draw for all worlds. -/
noncomputable def jointCounterfactualProb (E : (∀ v, α v) → Prop) [DecidablePred E]
    (hE : 0 < M.dist.probOf E) (X : κ → Finset V) (x : κ → ∀ v, α v)
    (Q : (κ → ∀ v, α v) → Prop) [DecidablePred Q] : ℝ :=
  ((M.noiseDist.cond (fun u => E (M.solve u)) (by rwa [← probOf_dist])).map
    fun u k => M.potentialResponse (X k) (x k) u).probOf Q

/-- The joint counterfactual probability in closed form:
`P(Q((V_{x k})_k) | E) = P_u(E(V(u)) ∧ Q((V_{x k}(u))_k)) / P(E)`. -/
theorem jointCounterfactualProb_eq (E : (∀ v, α v) → Prop) [DecidablePred E]
    (hE : 0 < M.dist.probOf E) (X : κ → Finset V) (x : κ → ∀ v, α v)
    (Q : (κ → ∀ v, α v) → Prop) [DecidablePred Q] :
    M.jointCounterfactualProb E hE X x Q =
      M.noiseDist.probOf (fun u => E (M.solve u) ∧ Q fun k => M.potentialResponse (X k) (x k) u) /
        M.dist.probOf E := by
  rw [jointCounterfactualProb, FiniteDist.probOf_map, FiniteDist.probOf_cond, probOf_dist]

/-- The marginals of the joint counterfactual probability: an event about the world `k` alone
has its single-intervention counterfactual probability. -/
theorem jointCounterfactualProb_eval (E : (∀ v, α v) → Prop) [DecidablePred E]
    (hE : 0 < M.dist.probOf E) (X : κ → Finset V) (x : κ → ∀ v, α v) (k : κ)
    (Q : (∀ v, α v) → Prop) [DecidablePred Q] :
    M.jointCounterfactualProb E hE X x (fun f => Q (f k)) =
      M.counterfactualProb E hE (X k) (x k) Q := by
  rw [jointCounterfactualProb_eq, counterfactualProb_eq]
  rfl

end SCM

/-! ### Same distributions, different counterfactuals -/

namespace SCMExamples

open SCM

/-- Probabilities under the fair coin. -/
theorem probOf_uniform_bool (P : Bool → Prop) [DecidablePred P] :
    (FiniteDist.uniform : FiniteDist Bool).probOf P =
      (if P true then 1 / 2 else 0) + (if P false then 1 / 2 else 0) := by
  unfold FiniteDist.probOf FiniteDist.prob
  rw [sum_filter, Fintype.sum_bool]
  simp

/-- Pearl's model 1 (Pearl 2009, (1.47) and Figure 1.6(b)): `X := U₁`, `Y := U₂` with two fair
coins; the treatment has no effect on anyone. -/
noncomputable def pearlModel1 : SCM arrow (fun _ => Bool) (fun _ => Bool) where
  acyclic := arrow_isAcyclic
  f _ _ e := e
  noise _ := FiniteDist.uniform

/-- Pearl's model 2 (Pearl 2009, (1.48) and Figure 1.6(c)): `X := U₁`,
`Y := X U₂ + (1 - X)(1 - U₂)`, that is `Y = 1` exactly when `X = U₂`, with two fair coins; the
treatment affects every subject. -/
noncomputable def pearlModel2 : SCM arrow (fun _ => Bool) (fun _ => Bool) where
  acyclic := arrow_isAcyclic
  f v z e := if h : v = 1 then decide (z ⟨0, by subst h; decide⟩ = e) else e
  noise _ := FiniteDist.uniform

theorem pearlModel1_kernel (v : Fin 2) (z) (a : Bool) : pearlModel1.kernel v z a = 1 / 2 := by
  rw [kernel_apply]
  change (FiniteDist.uniform : FiniteDist Bool).probOf (fun e => e = a) = 1 / 2
  rw [probOf_uniform_bool]
  cases a <;> norm_num

theorem pearlModel2_kernel (v : Fin 2) (z) (a : Bool) : pearlModel2.kernel v z a = 1 / 2 := by
  rw [kernel_apply]
  by_cases h : v = 1
  · subst h
    have hf : ∀ e, pearlModel2.f 1 z e = decide (z ⟨0, by decide⟩ = e) := fun e => rfl
    simp_rw [hf]
    change (FiniteDist.uniform : FiniteDist Bool).probOf
      (fun e => decide (z ⟨0, by decide⟩ = e) = a) = 1 / 2
    generalize z ⟨0, _⟩ = b
    rw [probOf_uniform_bool]
    cases a <;> cases b <;> norm_num
  · have hf : ∀ e, pearlModel2.f v z e = e := fun e => by simp [pearlModel2, h]
    simp_rw [hf]
    change (FiniteDist.uniform : FiniteDist Bool).probOf (fun e => e = a) = 1 / 2
    rw [probOf_uniform_bool]
    cases a <;> norm_num

/-- Both models induce the uniform distribution `P(x, y) = 1/4` (Pearl 2009, (1.47)). -/
theorem pearlModel1_dist (y : Fin 2 → Bool) : pearlModel1.dist y = 1 / 4 := by
  rw [dist_eq_prod, Fin.prod_univ_two]
  change pearlModel1.kernel 0 _ _ * pearlModel1.kernel 1 _ _ = _
  rw [pearlModel1_kernel, pearlModel1_kernel]
  norm_num

/-- The two models have the same observational distribution. -/
theorem pearlModel1_dist_eq : pearlModel1.dist = pearlModel2.dist :=
  dist_eq_of_kernel_eq _ fun v z a => by rw [pearlModel1_kernel, pearlModel2_kernel]

/-- The two models have the same interventional distribution for every intervention. -/
theorem pearlModel1_dist_intervene_eq (X : Finset (Fin 2)) (x : Fin 2 → Bool) :
    (pearlModel1.intervene X x).dist = (pearlModel2.intervene X x).dist := by
  ext y
  rw [dist_intervene, dist_intervene]
  congr 1
  refine prod_congr rfl fun v _ => ?_
  change pearlModel1.kernel v _ _ = pearlModel2.kernel v _ _
  rw [pearlModel1_kernel, pearlModel2_kernel]

theorem pearlModel1_solve (u : Fin 2 → Bool) : pearlModel1.solve u = u :=
  ((pearlModel1.isSolution_iff.1 fun _ => rfl)).symm

theorem pearlModel2_solve (u : Fin 2 → Bool) :
    pearlModel2.solve u = ![u 0, decide (u 0 = u 1)] := by
  refine (pearlModel2.isSolution_iff.1 fun v => ?_).symm
  fin_cases v <;> rfl

/-- The treatment value `X = 0` (written `false`), as a configuration. -/
def untreated : Fin 2 → Bool := fun _ => false

theorem pearlModel1_solve_intervene (u : Fin 2 → Bool) :
    (pearlModel1.intervene {0} untreated).solve u = ![false, u 1] := by
  refine ((pearlModel1.intervene {0} untreated).eq_solve_of_isSolution ?_).symm
  refine pearlModel1.isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton.1 hv]
    rfl
  · fin_cases v <;> simp_all [pearlModel1]

theorem pearlModel2_solve_intervene (u : Fin 2 → Bool) :
    (pearlModel2.intervene {0} untreated).solve u = ![false, decide (false = u 1)] := by
  refine ((pearlModel2.intervene {0} untreated).eq_solve_of_isSolution ?_).symm
  refine pearlModel2.isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton.1 hv]
    rfl
  · fin_cases v <;> simp_all [pearlModel2, Finset.restrict]

/-- The evidence `X = 1, Y = 1`: a treated subject who died. -/
def treatedDied (y : Fin 2 → Bool) : Prop := y 0 = true ∧ y 1 = true

instance : DecidablePred treatedDied := fun y => inferInstanceAs (Decidable (y 0 = true ∧ _))

theorem treatedDied_pos : 0 < pearlModel1.dist.probOf treatedDied := by
  refine lt_of_lt_of_le ?_ (pearlModel1.dist.le_probOf (fun _ => true) ⟨rfl, rfl⟩)
  rw [pearlModel1_dist]
  norm_num

theorem treatedDied_pos' : 0 < pearlModel2.dist.probOf treatedDied := by
  rw [← pearlModel1_dist_eq]
  exact treatedDied_pos

/-- In model 1, a treated subject who died would also have died untreated:
`P(Y_{X=0} = 0 | X = 1, Y = 1) = 0` (Pearl 2009, p. 36). -/
theorem pearlModel1_counterfactual :
    pearlModel1.counterfactualProb treatedDied treatedDied_pos {0} untreated
      (fun y => y 1 = false) = 0 := by
  rw [counterfactualProb_eq, FiniteDist.probOf_eq_zero, zero_div]
  intro u hu
  rw [pearlModel1_solve, pearlModel1_solve_intervene] at hu
  simp only [treatedDied, Matrix.cons_val_one] at hu
  rw [hu.1.2] at hu
  exact Bool.noConfusion hu.2

/-- In model 2, a treated subject who died would have recovered untreated:
`P(Y_{X=0} = 0 | X = 1, Y = 1) = 1` (Pearl 2009, p. 36). -/
theorem pearlModel2_counterfactual :
    pearlModel2.counterfactualProb treatedDied treatedDied_pos' {0} untreated
      (fun y => y 1 = false) = 1 := by
  rw [counterfactualProb_eq, probOf_dist]
  rw [FiniteDist.probOf_congr _ (Q := fun u => treatedDied (pearlModel2.solve u)) fun u => by
    rw [pearlModel2_solve, pearlModel2_solve_intervene]
    simp only [treatedDied, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      have h1 : u 1 = true := by
        rw [h.1] at h
        simpa using h.2.symm
      simp [h1]]
  rw [← probOf_dist]
  exact div_self treatedDied_pos'.ne'

end SCMExamples

end CausalInference
