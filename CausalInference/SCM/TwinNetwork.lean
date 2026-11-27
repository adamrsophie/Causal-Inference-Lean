/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Counterfactuals
public import CausalInference.SCM.Effects
public import CausalInference.Graphical.GlobalMarkov

/-!
# The twin network and counterfactual independence

The twin network of Balke and Pearl (1994) represents a factual world and a counterfactual world
under `do(X := x)` in one model: two copies of the endogenous variables share the noise
variables, and the arrows into the counterfactual copy of `X` (including those from the noises of
`X`) are cut. Here the shared noises are extra root vertices.

## Main definitions

* `SCM.twinGraph G X`: the twin graph on `V ⊕ V ⊕ V` (noise vertices, factual copy,
  counterfactual copy).
* `SCM.twin M X x`: the twin model, an `SCM` on the twin graph.
* `SCM.twinConfig M X x u`: the noise `u`, the factual solution `V(u)` and the counterfactual
  solution `V_x(u)` as one configuration of the twin graph.
* `SCM.cfJointDist M X x`: the joint law of `(V(u), V_x(u))`, a distribution on pairs.

## Main results

* `SCM.twin_solve`, `SCM.twin_dist`: the solution of the twin model is `twinConfig`, so its
  induced distribution is the law of `twinConfig M X x u` under the noise law of `M`.
* `SCM.twin_dist_map_twinPair` (**twin network theorem**, Pearl 2009, section 7.1.4): the
  induced distribution of the twin model, marginalized to the two copies, is `cfJointDist`.
* `SCM.counterfactualProb_eq_cond_cfJointDist`, `SCM.counterfactualProb_eq_cond_twin`: the
  counterfactual probability `P(Q(V_x) | E)` is a conditional probability under the joint law
  of the two worlds, and under the distribution of the twin model.
* `SCM.condIndep_twinConfig_of_dSep`: a d-separation in the twin graph gives a conditional
  independence between noise, factual and counterfactual variables (global Markov property of
  the twin model); `SCM.condIndepFun_twinConfig_of_dSep` states it for the corresponding
  random variables of the noise, with any conditioning set (used with a nonempty one in
  `SCM.chain_condIndepFun_cf_noise`).
* `SCM.chain_condIndepFun_cf` (Pearl 2009, Figure 7.3): in every model on the chain
  `X → Z → Y`, `Y_x ⫫ X`. `SCM.TwinChainExample.chainModel_not_condIndepFun`: a concrete model
  in which `Y_x ⫫ X | Z` fails; `SCM.chain_twin_not_dSep` is the open path in the twin graph.
* `SCM.exclusion_restriction` (Pearl 2009, Rule 1, (7.25)): `V_{pa_V, z}(u) = V_{pa_V}(u)`.
* `SCM.map_noiseDist_parentResponses`, `SCM.condIndepFun_parentResponses` (Pearl 2009, Rule 2,
  (7.26), for Markovian models): the counterfactuals `V_{pa_V}` of all vertices are mutually
  independent, with the kernels as laws.
* `SCM.condIndepFun_intervene_singleton_parents` (counterfactual reading of the back-door
  criterion, Pearl 2009, section 11.3.2, for the admissible set of parents): `V_x ⫫ X | PA_X`.
  `SCM.condIndepFun_intervene_singleton_parents_family` and `..._pair`: the joint version for
  a family of interventions, `(V_{x_k})_k ⫫ X | PA_X`, as in equation (11.4).
* `SCM.isAncestor_of_solve_intervene_ne` (recursiveness, Pearl 2009, Definition 7.3.4):
  counterfactual influence of `i` on `j` requires a directed path from `i` to `j`.
* `FiniteDist.probOf_pi_and_of_indep`: under a product law, a coordinate is independent of every
  event that does not depend on it.

The value and noise types `α` and `ε` live in one universe, because the twin model has both as
value types.

Sources: Balke and Pearl (1994); Pearl (2009), *Causality*, 2nd edition, sections 7.1.4, 7.3.1,
7.3.2 and 11.3.2.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace FiniteDist

variable {Ω Ω' β γ δ : Type*} [Fintype Ω] [Fintype Ω'] [DecidableEq Ω'] [DecidableEq β]
  [DecidableEq γ] [DecidableEq δ]

/-- Conditional independence under a pushforward is conditional independence of the composed
random variables. -/
theorem condIndepFun_map_iff (p : FiniteDist Ω) (g : Ω → Ω') (X : Ω' → β) (Y : Ω' → γ)
    (Z : Ω' → δ) : (p.map g).CondIndepFun X Y Z ↔ p.CondIndepFun (X ∘ g) (Y ∘ g) (Z ∘ g) := by
  unfold CondIndepFun
  simp only [probOf_map, Function.comp]

end FiniteDist

namespace SCM

universe u

variable {V : Type*}

/-! ### The twin graph -/

/-- The twin graph of `G` for an intervention on `X`, on the vertex type `V ⊕ V ⊕ V`. A vertex
`Sum.inl v` is the noise `U_v` of `v`, `Sum.inr (Sum.inl v)` is the factual copy of `v` and
`Sum.inr (Sum.inr v)` is its counterfactual copy `v*`. Each noise vertex is a root with an edge
into the factual copy of its vertex and, unless the vertex is in `X`, into its counterfactual
copy. The factual copy repeats the edges of `G`; the counterfactual copy repeats the edges of `G`
except those entering `X` (Pearl 2009, section 7.1.4, Figure 7.2). -/
def twinGraph (G : Digraph V) (X : Finset V) : Digraph (V ⊕ V ⊕ V) where
  Adj a b := match a, b with
    | .inl u, .inr (.inl v) => u = v
    | .inl u, .inr (.inr v) => u = v ∧ v ∉ X
    | .inr (.inl u), .inr (.inl v) => G.Adj u v
    | .inr (.inr u), .inr (.inr v) => G.Adj u v ∧ v ∉ X
    | _, _ => False

variable {G : Digraph V} {X : Finset V}

instance [DecidableEq V] [DecidableRel G.Adj] : DecidableRel (twinGraph G X).Adj := fun a b =>
  match a, b with
  | .inl _, .inl _ => inferInstanceAs (Decidable False)
  | .inl u, .inr (.inl v) => inferInstanceAs (Decidable (u = v))
  | .inl u, .inr (.inr v) => inferInstanceAs (Decidable (u = v ∧ v ∉ X))
  | .inr (.inl _), .inl _ => inferInstanceAs (Decidable False)
  | .inr (.inl u), .inr (.inl v) => inferInstanceAs (Decidable (G.Adj u v))
  | .inr (.inl _), .inr (.inr _) => inferInstanceAs (Decidable False)
  | .inr (.inr _), .inl _ => inferInstanceAs (Decidable False)
  | .inr (.inr _), .inr (.inl _) => inferInstanceAs (Decidable False)
  | .inr (.inr u), .inr (.inr v) => inferInstanceAs (Decidable (G.Adj u v ∧ v ∉ X))

theorem twinGraph_adj_noise_fact {u v : V} :
    (twinGraph G X).Adj (.inl u) (.inr (.inl v)) ↔ u = v := Iff.rfl

theorem twinGraph_adj_noise_cf {u v : V} :
    (twinGraph G X).Adj (.inl u) (.inr (.inr v)) ↔ u = v ∧ v ∉ X := Iff.rfl

theorem twinGraph_adj_fact_fact {u v : V} :
    (twinGraph G X).Adj (.inr (.inl u)) (.inr (.inl v)) ↔ G.Adj u v := Iff.rfl

theorem twinGraph_adj_cf_cf {u v : V} :
    (twinGraph G X).Adj (.inr (.inr u)) (.inr (.inr v)) ↔ G.Adj u v ∧ v ∉ X := Iff.rfl

/-- The twin graph of an acyclic graph is acyclic: a topological order of `G`, shifted by one on
both copies, with the noise vertices at the bottom, is a topological order of the twin graph. -/
theorem twinGraph_isAcyclic [Finite V] (hG : G.IsAcyclic) (X : Finset V) :
    (twinGraph G X).IsAcyclic := by
  obtain ⟨f, hf⟩ := hG.exists_adj_lt
  refine Digraph.isAcyclic_of_adj_lt
    (fun t => Sum.elim (fun _ => 0) (Sum.elim (fun v => f v + 1) (fun v => f v + 1)) t) ?_
  rintro (a | a | a) (b | b | b) h <;> simp_all [twinGraph]

/-! ### The twin model -/

/-- The value types of the twin model: the noise type `ε v` at the noise vertex of `v`, and the
value type `α v` at both copies of `v`. -/
abbrev twinVal (α ε : V → Type u) : V ⊕ V ⊕ V → Type u := Sum.elim ε (Sum.elim α α)

/-- The noise types of the twin model: the noise vertex of `v` carries the noise `ε v`; the two
copies carry no noise of their own (the one-point type). -/
abbrev twinNoise (ε : V → Type u) : V ⊕ V ⊕ V → Type u := Sum.elim ε (fun _ => PUnit)

variable {α ε : V → Type u}

instance [∀ v, Fintype (α v)] [∀ v, Fintype (ε v)] : ∀ t, Fintype (twinVal α ε t)
  | .inl v => inferInstanceAs (Fintype (ε v))
  | .inr (.inl v) => inferInstanceAs (Fintype (α v))
  | .inr (.inr v) => inferInstanceAs (Fintype (α v))

instance [∀ v, DecidableEq (α v)] [∀ v, DecidableEq (ε v)] : ∀ t, DecidableEq (twinVal α ε t)
  | .inl v => inferInstanceAs (DecidableEq (ε v))
  | .inr (.inl v) => inferInstanceAs (DecidableEq (α v))
  | .inr (.inr v) => inferInstanceAs (DecidableEq (α v))

instance [∀ v, Fintype (ε v)] : ∀ t, Fintype (twinNoise ε t)
  | .inl v => inferInstanceAs (Fintype (ε v))
  | .inr _ => inferInstanceAs (Fintype PUnit)

instance [∀ v, DecidableEq (ε v)] : ∀ t, DecidableEq (twinNoise ε t)
  | .inl v => inferInstanceAs (DecidableEq (ε v))
  | .inr _ => inferInstanceAs (DecidableEq PUnit)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [∀ v, Fintype (ε v)]

/-- The structural function of the twin model. The noise vertex of `v` copies its noise; the
factual copy of `v` applies `M.f v` to the factual copies of its parents and the noise vertex of
`v`; the counterfactual copy of `v` is the constant `x v` when `v ∈ X`, and otherwise applies
`M.f v` to the counterfactual copies of its parents and the noise vertex of `v`. -/
def twinF (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v) :
    ∀ t, (∀ p : (twinGraph G X).parentsFinset t, twinVal α ε p) → twinNoise ε t → twinVal α ε t
  | .inl _, _, e => e
  | .inr (.inl v), z, _ =>
    M.f v (fun p => z ⟨.inr (.inl p.1), Digraph.mem_parentsFinset.2
        (twinGraph_adj_fact_fact.2 (Digraph.mem_parentsFinset.1 p.2))⟩)
      (z ⟨.inl v, Digraph.mem_parentsFinset.2 (twinGraph_adj_noise_fact.2 rfl)⟩)
  | .inr (.inr v), z, _ =>
    if hv : v ∈ X then x v else
    M.f v (fun p => z ⟨.inr (.inr p.1), Digraph.mem_parentsFinset.2
        (twinGraph_adj_cf_cf.2 ⟨Digraph.mem_parentsFinset.1 p.2, hv⟩)⟩)
      (z ⟨.inl v, Digraph.mem_parentsFinset.2 (twinGraph_adj_noise_cf.2 ⟨rfl, hv⟩)⟩)

/-- The noise laws of the twin model: the law `M.noise v` at the noise vertex of `v`, and the
point mass at the two copies. -/
def twinNoiseLaw (M : SCM G α ε) : ∀ t, FiniteDist (twinNoise ε t)
  | .inl v => M.noise v
  | .inr _ => (FiniteDist.pure PUnit.unit : FiniteDist PUnit)

/-- The **twin model** of `M` for the intervention `do(X := x)` (Balke and Pearl 1994; Pearl
2009, section 7.1.4): a structural causal model on the twin graph. The noise vertices carry the
noises of `M` with their laws; the factual copy follows the equations of `M` and the
counterfactual copy those of the submodel `M_x`, both reading the same noise vertices. -/
def twin (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v) :
    SCM (twinGraph G X) (twinVal α ε) (twinNoise ε) where
  acyclic := twinGraph_isAcyclic M.acyclic X
  f := twinF M X x
  noise := twinNoiseLaw M

/-- The configuration of the twin model built from a noise value `u` of `M`: the noise `u v` at
the noise vertex of `v`, the factual solution `V(u)` on the factual copy and the counterfactual
solution `V_x(u)` on the counterfactual copy. -/
noncomputable def twinConfig (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v) (u : ∀ v, ε v) :
    ∀ t, twinVal α ε t
  | .inl v => u v
  | .inr (.inl v) => M.solve u v
  | .inr (.inr v) => (M.intervene X x).solve u v

/-- The noise value of `M` read off the noise vertices of a noise value of the twin model. -/
def twinNoiseProj (w : ∀ t, twinNoise ε t) : ∀ v, ε v := fun v => w (.inl v)

/-- The solution of the twin model: the noise vertices keep their noise, the factual copy is the
solution of `M` and the counterfactual copy is the solution of `M_x`, at the noise read off the
noise vertices. -/
theorem twin_solve (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v) (w : ∀ t, twinNoise ε t) :
    (M.twin X x).solve w = twinConfig M X x (twinNoiseProj w) := by
  refine ((M.twin X x).eq_solve_of_isSolution fun t => ?_).symm
  rcases t with v | v | v
  · rfl
  · exact M.solve_eq _ v
  · by_cases hv : v ∈ X
    · change (M.intervene X x).solve _ v = dite _ _ _
      simp only [hv, ↓reduceDIte]
      exact M.solve_intervene_of_mem _ hv
    · change (M.intervene X x).solve _ v = dite _ _ _
      simp only [hv, ↓reduceDIte]
      exact M.solve_intervene_of_notMem _ hv

variable [∀ v, DecidableEq (ε v)]

/-- The rectangle of twin noise values whose noise vertices carry `u`. -/
def twinNoiseRect (u : ∀ v, ε v) : ∀ t, Finset (twinNoise ε t)
  | .inl v => {u v}
  | .inr _ => univ

/-- The noise vertices of the twin model carry the noise law of `M`: the law of the noise read
off the noise vertices is `M.noiseDist`. -/
theorem twin_noiseDist_map (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v) :
    (M.twin X x).noiseDist.map twinNoiseProj = M.noiseDist := by
  ext u
  rw [FiniteDist.map_apply_eq_prob]
  have h : (univ.filter fun w => twinNoiseProj w = u) =
      Fintype.piFinset (twinNoiseRect u) := by
    ext w
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, funext_iff, twinNoiseProj]
    constructor
    · rintro h (v | t)
      · exact mem_singleton.2 (h v)
      · exact mem_univ _
    · intro h v
      exact mem_singleton.1 (h (.inl v))
  rw [h, noiseDist, FiniteDist.prob_piFinset, Fintype.prod_sum_type]
  have h2 : ∏ t : V ⊕ V, ((M.twin X x).noise (.inr t)).prob (twinNoiseRect u (.inr t)) = 1 :=
    prod_eq_one fun t _ => FiniteDist.prob_univ _
  rw [h2, mul_one]
  refine prod_congr rfl fun v _ => ?_
  exact sum_singleton _ _

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

/-- **The twin network represents the joint law of the factual and counterfactual worlds**: the
distribution induced by the twin model is the law of the configuration made of the noise `u`,
the factual solution `V(u)` and the counterfactual solution `V_x(u)`, when `u` has the noise law
of `M` (Pearl 2009, section 7.1.4). -/
theorem twin_dist (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v) :
    (M.twin X x).dist = M.noiseDist.map (twinConfig M X x) := by
  rw [dist, show (M.twin X x).solve = twinConfig M X x ∘ twinNoiseProj from
    funext (twin_solve M X x), ← FiniteDist.map_map, twin_noiseDist_map]

/-- The joint law of the factual solution and the counterfactual solution under `do(X := x)`,
both computed at the same noise value, as a distribution on pairs of configurations: the law of
`(V(u), V_x(u))` when `u` has the noise law of `M`. -/
noncomputable def cfJointDist (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v) :
    FiniteDist ((∀ v, α v) × (∀ v, α v)) :=
  M.noiseDist.map fun u => (M.solve u, (M.intervene X x).solve u)

/-- The factual and counterfactual copies of a configuration of the twin model, as a pair. -/
def twinPair (y : ∀ t, twinVal α ε t) : (∀ v, α v) × (∀ v, α v) :=
  (fun v => y (.inr (.inl v)), fun v => y (.inr (.inr v)))

/-- **Twin network theorem**: the distribution induced by the twin model, marginalized to the
factual and counterfactual copies, is the joint law of the factual and counterfactual solutions
(Pearl 2009, section 7.1.4, Figures 7.2 and 7.3). -/
theorem twin_dist_map_twinPair (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v) :
    (M.twin X x).dist.map twinPair = M.cfJointDist X x := by
  rw [twin_dist, FiniteDist.map_map]
  rfl

omit [∀ v, DecidableEq (ε v)] in
/-- The factual marginal of the joint law: the probability of factual evidence `E(V)` under
`cfJointDist` is its probability `P_M(E)` under the observational distribution. -/
theorem probOf_cfJointDist_fst (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v)
    (E : (∀ v, α v) → Prop) [DecidablePred E] :
    (M.cfJointDist X x).probOf (fun p => E p.1) = M.dist.probOf E := by
  rw [cfJointDist, FiniteDist.probOf_map, probOf_dist]

omit [∀ v, DecidableEq (ε v)] in
/-- **Counterfactual queries as conditional probabilities of the joint law** (Balke and Pearl
1994; Pearl 2009, section 7.1.4): for factual evidence `E` of positive probability, the
counterfactual probability `P(Q(V_x) | E)` computed by abduction, action and prediction is the
conditional probability of `Q` on the counterfactual copy given `E` on the factual copy, under
the joint law `cfJointDist` of the two worlds. -/
theorem counterfactualProb_eq_cond_cfJointDist (M : SCM G α ε) (E : (∀ v, α v) → Prop)
    [DecidablePred E] (hE : 0 < M.dist.probOf E) (X : Finset V) (x : ∀ v, α v)
    (Q : (∀ v, α v) → Prop) [DecidablePred Q] :
    M.counterfactualProb E hE X x Q = ((M.cfJointDist X x).cond (fun p => E p.1)
      (by rwa [probOf_cfJointDist_fst])).probOf (fun p => Q p.2) := by
  rw [FiniteDist.probOf_cond, probOf_cfJointDist_fst, counterfactualProb_eq, cfJointDist,
    FiniteDist.probOf_map]

omit [∀ v, DecidableEq (ε v)] in
/-- The joint law of the factual world and the world of `do(X := x)` is a marginal of the joint
law of a family of potential responses (`SCM.cfFamilyDist`): the family indexed by `Bool` with
the empty intervention (the factual world) at `false` and `do(X := x)` at `true`. -/
theorem cfJointDist_eq_map_cfFamilyDist (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v) :
    M.cfJointDist X x = (M.cfFamilyDist (fun b : Bool => if b then X else ∅) (fun _ => x)).map
      fun f => (f false, f true) := by
  rw [cfJointDist, cfFamilyDist, FiniteDist.map_map]
  congr 1
  funext u
  simp [potentialResponse_eq, solve_intervene_empty]

/-- **Counterfactual queries in the twin network**: the counterfactual probability
`P(Q(V_x) | E)` is the conditional probability, under the distribution induced by the twin
model, of `Q` on the counterfactual copy given `E` on the factual copy. -/
theorem counterfactualProb_eq_cond_twin (M : SCM G α ε) (E : (∀ v, α v) → Prop)
    [DecidablePred E] (hE : 0 < M.dist.probOf E) (X : Finset V) (x : ∀ v, α v)
    (Q : (∀ v, α v) → Prop) [DecidablePred Q] :
    M.counterfactualProb E hE X x Q = ((M.twin X x).dist.cond (fun y => E (twinPair y).1)
      (by rwa [← FiniteDist.probOf_map (M.twin X x).dist twinPair (fun p => E p.1),
        twin_dist_map_twinPair, probOf_cfJointDist_fst])).probOf (fun y => Q (twinPair y).2) := by
  rw [counterfactualProb_eq_cond_cfJointDist, FiniteDist.probOf_cond, FiniteDist.probOf_cond,
    ← twin_dist_map_twinPair, FiniteDist.probOf_map, FiniteDist.probOf_map]

/-- **d-separation in the twin graph gives counterfactual independence** (Pearl 2009,
section 7.1.4): if `A` and `B` are d-separated by `C` in the twin graph, then, under the joint
law of the noise, the factual solution and the counterfactual solution, the coordinates in `A`
and in `B` are conditionally independent given those in `C`. This is the global Markov property
of the twin model. -/
theorem condIndep_twinConfig_of_dSep (M : SCM G α ε) (X : Finset V) (x : ∀ v, α v)
    {A B C : Finset (V ⊕ V ⊕ V)} (h : (twinGraph G X).DSep ↑A ↑B ↑C) :
    (M.noiseDist.map (twinConfig M X x)).CondIndep A B C := by
  rw [← twin_dist]
  exact (M.twin X x).factorizes.condIndep_of_dSep (M.twin X x).acyclic h

omit [∀ v, Fintype (α v)] in
/-- **d-separation in the twin graph gives conditional independence of counterfactual random
variables**: if `A` and `B` are d-separated by `C` in the twin graph (`C` may be any set, in
particular a nonempty one), then under the noise law of `M` the twin-network coordinates in `A`
and in `B`, as functions of the noise, are conditionally independent given those in `C`. -/
theorem condIndepFun_twinConfig_of_dSep [∀ v, Finite (α v)] (M : SCM G α ε) (X : Finset V)
    (x : ∀ v, α v) {A B C : Finset (V ⊕ V ⊕ V)} (h : (twinGraph G X).DSep ↑A ↑B ↑C) :
    M.noiseDist.CondIndepFun (fun u => A.restrict (twinConfig M X x u))
      (fun u => B.restrict (twinConfig M X x u)) (fun u => C.restrict (twinConfig M X x u)) :=
  have : ∀ v, Fintype (α v) := fun _ => Fintype.ofFinite _
  (FiniteDist.condIndepFun_map_iff M.noiseDist (twinConfig M X x) (A.restrict (π := twinVal α ε))
    (B.restrict (π := twinVal α ε)) (C.restrict (π := twinVal α ε))).1
    (condIndep_twinConfig_of_dSep M X x h)

end SCM

namespace FiniteDist

variable {T : Type*} [Fintype T] [DecidableEq T] {β : T → Type*} [∀ t, Fintype (β t)]
  [∀ t, DecidableEq (β t)]

/-- Conditional independence of two single coordinates given the empty set, as independence of
the coordinate random variables (with a constant conditioning variable). -/
theorem CondIndep.condIndepFun_singleton_empty {p : FiniteDist (∀ t, β t)} {a b : T}
    (h : p.CondIndep {a} {b} ∅) : p.CondIndepFun (fun y => y a) (fun y => y b) (fun _ => ()) := by
  have h1 := (CondIndepFun.of_left h (fun c => c ⟨a, mem_singleton_self a⟩) fun _ => rfl).of_right
    (fun c => c ⟨b, mem_singleton_self b⟩) fun _ => rfl
  exact h1.of_cond (fun _ s => absurd s.2 (notMem_empty _)) (fun _ => ())
    (fun _ => funext fun s => absurd s.2 (notMem_empty _)) fun _ => rfl

end FiniteDist

namespace SCM

/-! ### The chain `X → Z → Y` -/

section Chain

open GraphExamples

variable {α ε : Fin 3 → Type u} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
  [∀ v, Fintype (ε v)] [∀ v, DecidableEq (ε v)]

/-- In the twin graph of the chain `0 → 1 → 2` for an intervention on `0`, the factual `0` and the
counterfactual `2*` are d-separated by the empty set. -/
theorem chain_twin_dSep :
    (twinGraph chain {0}).DSep ↑({.inr (.inl 0)} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3))
      ↑({.inr (.inr 2)} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3))
      ↑(∅ : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3)) := by
  simp only [coe_singleton, coe_empty]
  decide

/-- Conditioning on the factual middle vertex `1` d-connects the factual `0` and the
counterfactual `2*` in the twin graph of the chain: the factual `1` is a collider on the path
`0 → 1 ← U_1 → 1* → 2*`. -/
theorem chain_twin_not_dSep :
    ¬ (twinGraph chain {0}).DSep ↑({.inr (.inl 0)} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3))
      ↑({.inr (.inr 2)} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3))
      ↑({.inr (.inl 1)} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3)) := by
  simp only [coe_singleton]
  decide

/-- In the twin graph of the chain `0 → 1 → 2` for an intervention on `0`, the factual `0` and the
counterfactual `2*` are d-separated by the factual `1` together with its noise `U_1`: the collider
at the factual `1` is opened, but the path `0 → 1 ← U_1 → 1* → 2*` is blocked at `U_1`. -/
theorem chain_twin_dSep_noise :
    (twinGraph chain {0}).DSep ↑({.inr (.inl 0)} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3))
      ↑({.inr (.inr 2)} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3))
      ↑({.inr (.inl 1), .inl 1} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3)) := by
  simp only [coe_singleton, coe_insert]
  decide

omit [∀ v, Fintype (α v)] in
/-- **`Y_x ⫫ X | Z, U_Z` in the chain**, through the twin network with a nonempty conditioning
set: in every model on the chain `X → Z → Y` (vertices `0 → 1 → 2`), the counterfactual `Y_x`
is conditionally independent of the factual `X` given the factual `Z` and its noise `U_Z`. Here
the coordinates are those of the twin configuration (`twinConfig`). Without `U_Z` the
independence fails (`TwinChainExample.chainModel_not_condIndepFun`). -/
theorem chain_condIndepFun_cf_noise [∀ v, Finite (α v)] (M : SCM chain α ε) (x : ∀ v, α v) :
    M.noiseDist.CondIndepFun
      (fun u => ({.inr (.inl 0)} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3)).restrict (twinConfig M {0} x u))
      (fun u => ({.inr (.inr 2)} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3)).restrict (twinConfig M {0} x u))
      (fun u => ({.inr (.inl 1), .inl 1} : Finset (Fin 3 ⊕ Fin 3 ⊕ Fin 3)).restrict
        (twinConfig M {0} x u)) :=
  condIndepFun_twinConfig_of_dSep M {0} x chain_twin_dSep_noise

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (ε v)] in
/-- **`Y_x ⫫ X` in the chain** (Pearl 2009, section 7.1.4, Figure 7.3): in every model on the
chain `X → Z → Y` (vertices `0 → 1 → 2`), the counterfactual `Y_x` is independent of the factual
`X`, for every value `x`. Derived from the d-separation in the twin graph. -/
theorem chain_condIndepFun_cf [∀ v, Finite (α v)] (M : SCM chain α ε) (x : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => M.solve u 0) (fun u => (M.intervene {0} x).solve u 2)
      (fun _ => ()) := by
  classical
  have : ∀ v, Fintype (α v) := fun v => Fintype.ofFinite _
  exact (FiniteDist.condIndepFun_map_iff _ _ _ _ _).1
    (condIndep_twinConfig_of_dSep M {0} x chain_twin_dSep).condIndepFun_singleton_empty

end Chain

/-! ### `Y_x ⫫ X | Z` fails in the chain -/

namespace TwinChainExample

open GraphExamples

theorem zero_mem_parentsFinset_one : (0 : Fin 3) ∈ chain.parentsFinset 1 :=
  Digraph.mem_parentsFinset.2 rfl

theorem one_mem_parentsFinset {v : Fin 3} (h0 : v ≠ 0) (h1 : v ≠ 1) :
    (1 : Fin 3) ∈ chain.parentsFinset v := by
  fin_cases v
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact Digraph.mem_parentsFinset.2 rfl

/-- A model on the chain `X → Z → Y` with fair noise bits: `X := U_X`, `Z := X xor U_Z`,
`Y := Z`. -/
noncomputable def chainModel : SCM chain (fun _ => Bool) (fun _ => Bool) where
  acyclic := by decide
  f v z e := if h0 : v = 0 then e else if h1 : v = 1 then
      xor (z ⟨0, by subst h1; exact zero_mem_parentsFinset_one⟩) e
    else z ⟨1, one_mem_parentsFinset h0 h1⟩
  noise _ := FiniteDist.uniform

theorem chainModel_solve (u : Fin 3 → Bool) :
    chainModel.solve u = ![u 0, xor (u 0) (u 1), xor (u 0) (u 1)] := by
  refine (chainModel.isSolution_iff.1 fun v => ?_).symm
  fin_cases v <;> simp [chainModel, Finset.restrict]

/-- The treatment value `X = false`, as a configuration. -/
def xFalse : Fin 3 → Bool := fun _ => false

theorem chainModel_solve_intervene (u : Fin 3 → Bool) :
    (chainModel.intervene {0} xFalse).solve u = ![false, u 1, u 1] := by
  refine ((chainModel.intervene {0} xFalse).eq_solve_of_isSolution ?_).symm
  refine chainModel.isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton.1 hv]
    rfl
  · fin_cases v <;> simp_all [chainModel, Finset.restrict]

/-- Probabilities of events depending on the first two noise bits of the chain model. -/
theorem probOf_noise_pair (P : Bool × Bool → Prop) [DecidablePred P] :
    chainModel.noiseDist.probOf (fun u => P (u 0, u 1)) =
      (if P (false, false) then 1 / 4 else 0) + (if P (false, true) then 1 / 4 else 0) +
        (if P (true, false) then 1 / 4 else 0) + (if P (true, true) then 1 / 4 else 0) := by
  rw [← FiniteDist.probOf_map chainModel.noiseDist (fun u => (u 0, u 1)) P]
  change ((FiniteDist.pi fun _ => FiniteDist.uniform).map fun u : Fin 3 → Bool => (u 0, u 1)).probOf
    P = _
  rw [FiniteDist.map_pi_eval_pair _ (by decide)]
  simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, FiniteDist.prod_apply, FiniteDist.uniform_apply, Fintype.card_bool]
  split_ifs <;> norm_num

/-- **`Y_x ⫫ X | Z` fails in the chain** (Pearl 2009, section 7.1.4, Figure 7.3): in the chain
model, the counterfactual `Y_{X = false}` is not independent of the factual `X` given the
factual `Z`. At `X = Y_x = Z = false` the product form reads `1/4 * 1/2 = 1/8` on the left and
`1/4 * 1/4 = 1/16` on the right. -/
theorem chainModel_not_condIndepFun :
    ¬ chainModel.noiseDist.CondIndepFun (fun u => chainModel.solve u 0)
      (fun u => (chainModel.intervene {0} xFalse).solve u 2) (fun u => chainModel.solve u 1) := by
  intro h
  have key := h false false false
  simp only [chainModel_solve, chainModel_solve_intervene, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at key
  rw [probOf_noise_pair (fun q => q.1 = false ∧ q.2 = false ∧ xor q.1 q.2 = false),
    probOf_noise_pair (fun q => xor q.1 q.2 = false),
    probOf_noise_pair (fun q => q.1 = false ∧ xor q.1 q.2 = false),
    probOf_noise_pair (fun q => q.2 = false ∧ xor q.1 q.2 = false)] at key
  norm_num at key

end TwinChainExample

end SCM


/-! ### Counterfactual independence from the graph -/

namespace FiniteDist

section PiIndep

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)]

omit [∀ i, DecidableEq (κ i)] in
/-- The coordinatewise pushforward of a product law is the product of the pushforwards. -/
theorem map_pi_map {κ' : ι → Type*} [∀ i, Fintype (κ' i)] [∀ i, DecidableEq (κ' i)]
    (p : ∀ i, FiniteDist (κ i)) (g : ∀ i, κ i → κ' i) :
    (pi p).map (fun ω i => g i (ω i)) = pi fun i => (p i).map (g i) := by
  ext b
  rw [map_apply_eq_prob]
  have h : (univ.filter fun ω : ∀ i, κ i => (fun i => g i (ω i)) = b) =
      Fintype.piFinset fun i => univ.filter fun e => g i e = b i := by
    ext ω
    simp [funext_iff]
  rw [h, prob_piFinset]
  rfl

omit [∀ i, DecidableEq (κ i)] in
/-- Cross-product identity for changing one coordinate of an outcome under a product law:
`P(ω[i := a]) * p_i(ω i) = P(ω) * p_i(a)`. It holds unconditionally; when `p_i(ω i) = 0` both
sides vanish and it says nothing about `P(ω[i := a])`, which may be positive. The ratio form,
under `0 < p_i(ω i)`, is `pi_update_eq_div`. -/
theorem pi_update_mul (p : ∀ i, FiniteDist (κ i)) (ω : ∀ i, κ i) (i : ι) (a : κ i) :
    pi p (Function.update ω i a) * p i (ω i) = pi p ω * p i a := by
  simp only [pi_apply]
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun j => p j (ω j)),
    Function.update_self]
  have : ∏ j ∈ ({i} : Finset ι)ᶜ, p j (Function.update ω i a j) = ∏ j ∈ ({i} : Finset ι)ᶜ,
      p j (ω j) :=
    prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (by simpa using hj)]
  rw [this]
  ring

omit [∀ i, DecidableEq (κ i)] in
/-- Changing one coordinate of an outcome multiplies its product mass by the ratio of the masses
of the two values of that coordinate: `P(ω[i := a]) = P(ω) * p_i(a) / p_i(ω i)`, when the
original value has positive mass `0 < p_i(ω i)`. -/
theorem pi_update_eq_div (p : ∀ i, FiniteDist (κ i)) (ω : ∀ i, κ i) (i : ι) (a : κ i)
    (h : 0 < p i (ω i)) : pi p (Function.update ω i a) = pi p ω * p i a / p i (ω i) := by
  rw [eq_div_iff h.ne', pi_update_mul]

omit [∀ i, DecidableEq (κ i)] in
/-- **Independence of one coordinate of a product law from the others**: if the event `E` does
not depend on the coordinate `i`, then
`P(ω i ∈ B ∧ E) = P_i(B) * P(E)` under the product law. -/
theorem probOf_pi_and_of_indep (p : ∀ i, FiniteDist (κ i)) (i : ι) (B : κ i → Prop)
    [DecidablePred B] (E : (∀ i, κ i) → Prop) [DecidablePred E]
    (hE : ∀ ω a, E (Function.update ω i a) ↔ E ω) :
    (pi p).probOf (fun ω => B (ω i) ∧ E ω) = (p i).probOf B * (pi p).probOf E := by
  classical
  -- the event at a single value `a` of the coordinate
  have hval : ∀ a b, (pi p).probOf (fun ω => ω i = a ∧ E ω) * p i b =
      (pi p).probOf (fun ω => ω i = b ∧ E ω) * p i a := by
    intro a b
    unfold probOf prob
    rw [sum_mul, sum_mul]
    refine sum_nbij' (fun ω => Function.update ω i b) (fun ω => Function.update ω i a)
      ?_ ?_ ?_ ?_ ?_
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      exact ⟨Function.update_self .., (hE ω b).2 hω.2⟩
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω ⊢
      exact ⟨Function.update_self .., (hE ω a).2 hω.2⟩
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      rw [Function.update_idem, ← hω.1, Function.update_eq_self]
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      rw [Function.update_idem, ← hω.1, Function.update_eq_self]
    · intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      have := pi_update_mul p ω i b
      rw [hω.1] at this
      rw [this]
  have hE' : (pi p).probOf E = ∑ b, (pi p).probOf (fun ω => ω i = b ∧ E ω) := by
    rw [probOf_eq_sum_univ (pi p) (fun ω => ω i)]
    exact sum_congr rfl fun b _ => probOf_congr _ fun ω => and_comm
  have hval' : ∀ a, (pi p).probOf (fun ω => ω i = a ∧ E ω) = p i a * (pi p).probOf E := by
    intro a
    rw [hE', mul_sum]
    have := fun b => hval a b
    calc (pi p).probOf (fun ω => ω i = a ∧ E ω)
        = (pi p).probOf (fun ω => ω i = a ∧ E ω) * ∑ b, p i b := by
          rw [(p i).sum_eq_one, mul_one]
      _ = ∑ b, p i a * (pi p).probOf (fun ω => ω i = b ∧ E ω) := by
          rw [mul_sum]
          exact sum_congr rfl fun b _ => by rw [this b, mul_comm]
  rw [probOf_eq_sum_univ (pi p) (fun ω => ω i) (P := fun ω => B (ω i) ∧ E ω)]
  unfold probOf prob
  rw [sum_filter, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  split_ifs with hB
  · rw [← prob, ← probOf, ← prob, ← probOf]
    rw [probOf_congr _ (Q := fun ω => ω i = a ∧ E ω) fun ω => ⟨fun h => ⟨h.2, h.1.2⟩,
      fun h => ⟨⟨h.1 ▸ hB, h.2⟩, h.1⟩⟩, hval']
  · rw [zero_mul]
    rw [← prob, ← probOf]
    exact probOf_eq_zero _ fun ω h => hB (h.2 ▸ h.1.1)

end PiIndep

end FiniteDist

namespace SCM

section Restrictions

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- Once all parents of `v` are fixed by intervention (and `v` itself is not), the value of `v`
is its structural function at the fixed parent values and its own noise:
`V_{pa_V}(u) = f_V(pa_V, u_V)`. -/
theorem solve_intervene_of_parents_subset {S : Finset V} {v : V} (hpa : G.parentsFinset v ⊆ S)
    (hv : v ∉ S) (x : ∀ v, α v) (u : ∀ v, ε v) :
    (M.intervene S x).solve u v = M.f v ((G.parentsFinset v).restrict x) (u v) := by
  rw [M.solve_intervene_of_notMem u hv]
  congr 1
  funext p
  exact M.solve_intervene_of_mem u (hpa p.2)

omit [DecidableEq V] in
include M in
theorem notMem_parentsFinset_self (v : V) : v ∉ G.parentsFinset v :=
  fun h => M.acyclic.irrefl v (Digraph.mem_parentsFinset.1 h)

/-- **Exclusion restrictions** (Pearl 2009, Rule 1, equation (7.25)): once the parents of `v`
are fixed, a further intervention on a set `Z` not containing `v` does not change `v`:
`V_{pa_V, z}(u) = V_{pa_V}(u)`. The values of the parents are those of `x`; Pearl states the
rule for `Z` disjoint from the parents, and the hypothesis `v ∉ Z` (implicit there) is needed,
since otherwise `V_{pa_V, z} = z`. -/
theorem exclusion_restriction (v : V) {Z : Finset V} (hvZ : v ∉ Z) (x z : ∀ v, α v)
    (u : ∀ v, ε v) :
    (M.intervene (G.parentsFinset v ∪ Z)
        (fun w => if w ∈ G.parentsFinset v then x w else z w)).solve u v =
      (M.intervene (G.parentsFinset v) x).solve u v := by
  rw [M.solve_intervene_of_parents_subset subset_union_left
      (by simp only [mem_union, not_or]; exact ⟨M.notMem_parentsFinset_self v, hvZ⟩),
    M.solve_intervene_of_parents_subset subset_rfl (M.notMem_parentsFinset_self v)]
  congr 1
  funext p
  simp only [Finset.restrict, p.2, ↓reduceIte]

/-- Under `do(X := x)` the solution does not depend on the noise of the vertices of `X`: two
noise values that agree outside `X` give the same counterfactual solution. -/
theorem solve_intervene_congr_noise {X : Finset V} (x : ∀ v, α v) {u u' : ∀ v, ε v}
    (h : ∀ v ∉ X, u v = u' v) : (M.intervene X x).solve u = (M.intervene X x).solve u' :=
  (M.intervene X x).eq_solve_of_isSolution (M.isSolution_intervene_iff.2
    ⟨fun v hv => M.solve_intervene_of_mem u hv, fun v hv => by
      rw [M.solve_intervene_of_notMem u hv, h v hv]⟩)

variable [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]

/-- **Independence restrictions** for Markovian models (Pearl 2009, Rule 2, equation (7.26)), in
product form: with the parents of each vertex `v` fixed at the values `x v`, the counterfactuals
`V_{pa_V}` of all vertices are mutually independent, and each has the law of its kernel. Their
joint law is the product of the kernels `M.kernel v (x v restricted to pa_V)`. In a Markovian
model all noises are independent, so no two vertices are joined by a path of noise variables. -/
theorem map_noiseDist_parentResponses (x : V → ∀ v, α v) :
    M.noiseDist.map (fun u v => (M.intervene (G.parentsFinset v) (x v)).solve u v) =
      FiniteDist.pi fun v => M.kernel v ((G.parentsFinset v).restrict (x v)) := by
  have h : (fun u v => (M.intervene (G.parentsFinset v) (x v)).solve u v) =
      fun u v => M.f v ((G.parentsFinset v).restrict (x v)) (u v) :=
    funext fun u => funext fun v =>
      M.solve_intervene_of_parents_subset subset_rfl (M.notMem_parentsFinset_self v) _ _
  rw [h, noiseDist, FiniteDist.map_pi_map]
  rfl

omit [∀ v, Fintype (α v)] in
/-- **Independence restrictions** (Pearl 2009, Rule 2, equation (7.26)), pairwise form: for two
distinct vertices `v` and `w`, the counterfactuals `V_{pa_V}` and `W_{pa_W}` are independent. -/
theorem condIndepFun_parentResponses [∀ v, Finite (α v)] {v w : V} (hvw : v ≠ w)
    (x y : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => (M.intervene (G.parentsFinset v) x).solve u v)
      (fun u => (M.intervene (G.parentsFinset w) y).solve u w) (fun _ => ()) := by
  simp_rw [M.solve_intervene_of_parents_subset subset_rfl (M.notMem_parentsFinset_self _)]
  rw [FiniteDist.condIndepFun_iff_exists_mul]
  refine ⟨fun a _ => (M.noise v).probOf (fun e => M.f v ((G.parentsFinset v).restrict x) e = a),
    fun b c => M.noiseDist.probOf
      (fun u => M.f w ((G.parentsFinset w).restrict y) (u w) = b ∧ () = c), fun a b c => ?_⟩
  dsimp only
  exact FiniteDist.probOf_pi_and_of_indep M.noise v
    (fun e => M.f v ((G.parentsFinset v).restrict x) e = a)
    (fun u => M.f w ((G.parentsFinset w).restrict y) (u w) = b ∧ () = c) fun u e => by
      simp only [Function.update_of_ne hvw.symm]

omit [∀ v, Fintype (α v)] in
/-- **Counterfactual reading of the back-door criterion with the parents** (Pearl 2009,
section 11.3.2, for the admissible set `Z = PA_X`): the whole counterfactual solution `V_x`
under `do(X := x)` for a single vertex `X` is conditionally independent of the factual value of
`X` given the factual values of the parents of `X`. In particular `Y_x ⫫ X | PA_X` for every
vertex `Y`. -/
theorem condIndepFun_intervene_singleton_parents [∀ v, Finite (α v)] (i : V) (x : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => M.solve u i) (fun u => (M.intervene {i} x).solve u)
      (fun u => (G.parentsFinset i).restrict (M.solve u)) := by
  have : ∀ v, Fintype (α v) := fun v => Fintype.ofFinite _
  have hpar : ∀ (u : ∀ v, ε v) (p : G.parentsFinset i),
      M.solve u p = (M.intervene {i} x).solve u p := by
    intro u p
    refine (M.solve_intervene_of_notMem_descendantsOf u fun h => ?_).symm
    obtain ⟨s, hs, hsp⟩ := Digraph.mem_descendantsOf.1 h
    rw [coe_singleton, Set.mem_singleton_iff] at hs
    subst hs
    exact M.acyclic s (Relation.TransGen.tail' hsp (Digraph.mem_parentsFinset.1 p.2))
  have hupd : ∀ (u : ∀ v, ε v) (e : ε i),
      (M.intervene {i} x).solve (Function.update u i e) = (M.intervene {i} x).solve u :=
    fun u e => M.solve_intervene_congr_noise x fun v hv =>
      Function.update_of_ne (fun h => hv (mem_singleton.2 h)) _ _
  rw [FiniteDist.condIndepFun_iff_exists_mul]
  refine ⟨fun a c => M.kernel i c a, fun b c => M.noiseDist.probOf
    (fun u => (M.intervene {i} x).solve u = b ∧ (G.parentsFinset i).restrict (M.solve u) = c),
    fun a b c => ?_⟩
  rw [FiniteDist.probOf_congr _ (Q := fun u => M.f i c (u i) = a ∧
      ((M.intervene {i} x).solve u = b ∧ (G.parentsFinset i).restrict (M.solve u) = c))
    fun u => by
      rw [M.solve_eq u i]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h3 ▸ h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h3 ▸ h1, h2, h3⟩]
  dsimp only
  refine FiniteDist.probOf_pi_and_of_indep M.noise i (fun e => M.f i c e = a)
    (fun u => (M.intervene {i} x).solve u = b ∧ (G.parentsFinset i).restrict (M.solve u) = c)
    fun u e => ?_
  have hz : (G.parentsFinset i).restrict (M.solve (Function.update u i e)) =
      (G.parentsFinset i).restrict (M.solve u) := by
    funext p
    simp only [Finset.restrict, hpar _ p, hupd]
  rw [hupd, hz]

omit [∀ v, Fintype (α v)] in
/-- **Joint counterfactual reading of the back-door criterion with the parents** (Pearl 2009,
section 11.3.2 and equation (11.4), for the admissible set `Z = PA_X`): for any finite family
of interventions `do(X := x k)` on a single vertex `X`, the whole family of counterfactual
solutions `(V_{x k})_k`, computed at one shared noise value, is conditionally independent of the
factual value of `X` given the factual values of the parents of `X`. This is a joint statement
about all potential responses at once; it does not follow from the independences for each
`k` separately. -/
theorem condIndepFun_intervene_singleton_parents_family [∀ v, Finite (α v)] {κ : Type*}
    [Fintype κ] (i : V) (x : κ → ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => M.solve u i) (fun u k => (M.intervene {i} (x k)).solve u)
      (fun u => (G.parentsFinset i).restrict (M.solve u)) := by
  classical
  have : ∀ v, Fintype (α v) := fun v => Fintype.ofFinite _
  have hpar : ∀ (u : ∀ v, ε v) (p : G.parentsFinset i) (y : ∀ v, α v),
      M.solve u p = (M.intervene {i} y).solve u p := by
    intro u p y
    refine (M.solve_intervene_of_notMem_descendantsOf u fun h => ?_).symm
    obtain ⟨s, hs, hsp⟩ := Digraph.mem_descendantsOf.1 h
    rw [coe_singleton, Set.mem_singleton_iff] at hs
    subst hs
    exact M.acyclic s (Relation.TransGen.tail' hsp (Digraph.mem_parentsFinset.1 p.2))
  have hupd : ∀ (u : ∀ v, ε v) (e : ε i),
      (fun k => (M.intervene {i} (x k)).solve (Function.update u i e)) =
        fun k => (M.intervene {i} (x k)).solve u :=
    fun u e => funext fun k => M.solve_intervene_congr_noise (x k) fun v hv =>
      Function.update_of_ne (fun h => hv (mem_singleton.2 h)) _ _
  rw [FiniteDist.condIndepFun_iff_exists_mul]
  refine ⟨fun a c => M.kernel i c a, fun b c => M.noiseDist.probOf
    (fun u => (fun k => (M.intervene {i} (x k)).solve u) = b ∧
      (G.parentsFinset i).restrict (M.solve u) = c), fun a b c => ?_⟩
  rw [FiniteDist.probOf_congr _ (Q := fun u => M.f i c (u i) = a ∧
      ((fun k => (M.intervene {i} (x k)).solve u) = b ∧
        (G.parentsFinset i).restrict (M.solve u) = c))
    fun u => by
      rw [M.solve_eq u i]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h3 ▸ h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h3 ▸ h1, h2, h3⟩]
  dsimp only
  refine FiniteDist.probOf_pi_and_of_indep M.noise i (fun e => M.f i c e = a)
    (fun u => (fun k => (M.intervene {i} (x k)).solve u) = b ∧
      (G.parentsFinset i).restrict (M.solve u) = c)
    fun u e => ?_
  have hz : (G.parentsFinset i).restrict (M.solve (Function.update u i e)) =
      (G.parentsFinset i).restrict (M.solve u) := by
    funext p
    simp only [Finset.restrict]
    rw [hpar _ p (M.solve u), M.solve_intervene_congr_noise (M.solve u)
      (u := Function.update u i e) (u' := u)
      (fun v hv => Function.update_of_ne (fun h => hv (mem_singleton.2 h)) _ _),
      ← hpar u p (M.solve u)]
  rw [hupd, hz]

omit [∀ v, Fintype (α v)] in
/-- **The pair of potential responses is independent of the treatment given its parents**
(Pearl 2009, section 11.3.2, equation (11.4), with `Z = PA_X`): for two interventions
`do(X := x)` and `do(X := x')` on a single vertex `X`, the pair `(V_x, V_{x'})` of counterfactual
solutions at one noise value is conditionally independent of the factual `X` given `PA_X`. -/
theorem condIndepFun_intervene_singleton_parents_pair [∀ v, Finite (α v)] (i : V)
    (x x' : ∀ v, α v) :
    M.noiseDist.CondIndepFun (fun u => M.solve u i)
      (fun u => ((M.intervene {i} x).solve u, (M.intervene {i} x').solve u))
      (fun u => (G.parentsFinset i).restrict (M.solve u)) := by
  have : ∀ v, Fintype (α v) := fun v => Fintype.ofFinite _
  exact (M.condIndepFun_intervene_singleton_parents_family i (fun k : Bool => if k then x else x')
    ).of_right (fun f => (f true, f false)) fun u => by simp

end Restrictions

section Influence

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} {ε : V → Type*} [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- **Counterfactual influence requires a directed path** (Pearl 2009, section 7.3.1 and
Definition 7.3.4, recursiveness): for distinct vertices `i` and `j`, a further intervention
`do(i := x)` on top of any intervention `do(W := w)` can change the value of `j` only if `i` is
a proper ancestor of `j` in the graph of the model: `j_{x, w}(u) ≠ j_w(u)` implies `i ⇝ j`.
Since the graph is acyclic, the relation of counterfactual influence has no cycles. The graph
of the model may have edges along which nothing is transmitted; the converse fails. -/
theorem isAncestor_of_solve_intervene_ne {i j : V} (hij : i ≠ j) (W : Finset V)
    (w x : ∀ v, α v) (u : ∀ v, ε v)
    (h : ((M.intervene W w).intervene {i} x).solve u j ≠ (M.intervene W w).solve u j) :
    G.IsAncestor i j := by
  by_contra hanc
  refine h ((M.intervene W w).solve_intervene_of_notMem_descendantsOf u ?_)
  rw [coe_singleton]
  exact notMem_descendantsOf_singleton hij fun h' =>
    hanc (Relation.TransGen.mono (r := (G.deleteIncoming (W : Set V)).Adj) (p := G.Adj)
      (fun _ _ hab => hab.1) i j h')

end Influence

end SCM

end CausalInference
