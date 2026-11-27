/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.DoCalculusExamples
public import CausalInference.Graphical.Criteria.FrontDoor
public import CausalInference.SCM.Counterfactuals
public import CausalInference.SCM.DoCalculusRule3

/-!
# Back-door and front-door adjustment

The graphical identification theorems of Pearl (2009), section 3.3, for a finite structural
causal model `M : SCM G α ε`, stated with the graphical criteria of the library
(`Digraph.BackDoor`, `Digraph.FrontDoor`). Latent variables are the vertices outside the query
sets; they are marginalized, so the statements cover semi-Markovian models.

## Main results

* `SCM.backdoor_stratum`: the division-free per-stratum identity behind the back-door formula,
  `P(y, z | do(x)) * P(x, z) = P(y, x, z) * P(z)`.
* `SCM.effect_eq_sum_of_backDoor` (**back-door adjustment**, Pearl 2009, Theorem 3.3.2,
  equation (3.19)): if `Z` satisfies the back-door criterion relative to `(X, Y)`, then
  `P(y | do(x)) = ∑_z P(y | x, z) P(z)`, under the positivity `P(z) > 0 → P(x, z) > 0`.
* `SCM.effect_eq_sum_parents`, `SCM.effect_eq_div_of_parents_eq_empty`: the parents of a single
  treatment are admissible; a treatment without parents needs no adjustment,
  `P(y | do(x)) = P(y | x)`.
* `SCM.identifiableFrom_effect_of_backDoor`: the effect is identifiable from any observed set
  containing `X ∪ Y ∪ Z`, within the class of models satisfying the positivity.
* `SCM.adjustment_eq_of_backDoor` (Pearl 2009, section 11.3.3, equation (11.8), p. 345:
  c-equivalence of admissible sets): two admissible sets give the same adjustment value.
* `SCM.ett_stratum`, `SCM.ett_joint_eq_sum_of_backDoor_of_overlap`,
  `SCM.ett_eq_sum_of_backDoor_of_overlap` (Pearl 2009, section 11.3.2, p. 344): for a single
  treatment and a back-door admissible `Z`, the division-free stratum identity
  `P(Y_x = y, x', z) P(x, z) = P(y, x, z) P(x', z)`, and the effect of treatment on the treated
  `P(Y_x = y | X = x') = ∑_z P(y | x, z) P(z | x')` under the overlap `P(x', z) > 0 → P(x, z) > 0`
  on the support of the treated group. `SCM.ett_joint_eq_sum_of_backDoor` and
  `SCM.ett_eq_sum_of_backDoor` are the corollaries under `P(z) > 0 → P(x, z) > 0`.
* `SCM.BowExample.adjustment_empty_ne_effect`: adjustment for an inadmissible set (the empty set
  in the bow graph) gives `3/4` while the effect is `1/2`.
* `SCM.effect_eq_sum_of_frontDoor` (**front-door adjustment**, Pearl 2009, Theorem 3.3.4,
  equation (3.29)): if `Z` satisfies the front-door criterion relative to `(X, Y)` and the law of
  `(X, Z)` is strictly positive, then `P(y | do(x)) = ∑_z P(z | x) ∑_x' P(y | x', z) P(x')`, for
  arbitrary sets `X`, `Y`, `Z` and any graph. `SCM.frontdoor_stratum` is the division-free
  identity behind it, `SCM.frontdoor_stratum_div` its divided form under `P(x) > 0` (which
  `SCM.CopyChainExample.frontdoor_stratum_div_ne` shows is needed), and
  `SCM.identifiableFrom_effect_of_frontDoor` the identifiability statement.

All values are read off configurations: `P(s)` at a configuration `c` is the marginal mass
`M.dist.margAt S c`, and sums over `z` run over the configurations that agree with a given one
outside `Z`.

Sources: Pearl (2009), *Causality*, 2nd edition, sections 3.3.1 to 3.3.3 and 11.3.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace FiniteDist

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)]

/-- Two joint laws with the same marginal on `O` have the same marginal masses on every subset
of `O`. -/
theorem margAt_eq_of_marginal_eq {p q : FiniteDist (∀ v, α v)} {O S : Finset V}
    (h : p.marginal O = q.marginal O) (hS : S ⊆ O) (c : ∀ v, α v) :
    p.margAt S c = q.margAt S c := by
  rw [← marginal_restrict, ← marginal_restrict, ← marginal_marginal p hS,
    ← marginal_marginal q hS, h]

end FiniteDist

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-! ### The back-door criterion: consequences used below -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Condition (i) of the back-door criterion makes `X` and `Z` disjoint. -/
theorem disjoint_of_backDoor {X Y Z : Finset V} (h : G.BackDoor ↑X ↑Y ↑Z) : Disjoint X Z :=
  disjoint_left.2 fun _ hx hz => h.1 _ (mem_coe.2 hz) (Digraph.subset_descendantsOf _ hx)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The back-door criterion makes `X` and `Y` disjoint. -/
theorem disjoint_left_of_backDoor {X Y Z : Finset V} (h : G.BackDoor ↑X ↑Y ↑Z) :
    Disjoint X Y :=
  disjoint_left.2 fun _ hx hy =>
    disjoint_left.1 (disjoint_of_backDoor h) hx (h.2.inter_subset ⟨hx, hy⟩)

/-! ### Back-door adjustment -/

/-- The division-free per-stratum identity behind the back-door formula: if `Z` satisfies the
back-door criterion relative to `(X, Y)`, then at every
configuration `c`, `P(y, z | do(x)) * P(x, z) = P(y, x, z) * P(z)`, all values read off `c`. No
positivity is needed. -/
theorem backdoor_stratum {X Y Z : Finset V} (hbd : G.BackDoor ↑X ↑Y ↑Z) (c : ∀ u, α u) :
    (M.intervene X c).dist.margAt (Y ∪ Z) c * M.dist.margAt (X ∪ Z) c =
      M.dist.margAt (Y ∪ X ∪ Z) c * M.dist.margAt Z c := by
  have hsep' : ((G.deleteIncoming ↑(∅ : Finset V)).deleteOutgoing ↑X).DSep ↑Y ↑X
      ↑((∅ : Finset V) ∪ Z) := by
    simpa using hbd.2.symm
  have h2 := M.rule2 c (disjoint_empty_left X) (disjoint_left_of_backDoor hbd).symm
    (disjoint_of_backDoor hbd).symm hsep'
  rw [M.dist_intervene_of_eq (empty_union X)] at h2
  simp only [dist_intervene_empty] at h2
  rwa [M.margAt_intervene_of_notMem_descendantsOf (fun u hu => hbd.1 u (mem_coe.2 hu)) c] at h2

/-- **Back-door adjustment** (Pearl 2009, Theorem 3.3.2, equation (3.19)), with the back-door
criterion of the library (`Digraph.BackDoor`). If `Z` satisfies the back-door criterion relative
to `(X, Y)`, `Y` is disjoint from `Z`, and every value `z` of positive probability gives the
treatment value `x` positive probability together with it (`P(z) > 0 → P(x, z) > 0`), then
`P(y | do(x)) = ∑_z P(y, x, z) / P(x, z) * P(z)`, that is `∑_z P(y | x, z) P(z)`. The sum runs
over the configurations that agree with `v` outside `Z`; values `z` of probability zero
contribute zero on both sides.

The disjointness of `X` from `Y` and from `Z` follows from the criterion. The disjointness of `Y`
and `Z` is an extra hypothesis (Pearl's sets are disjoint): the sum ranges over the coordinates
of `Z` while `y` is held fixed. -/
theorem effect_eq_sum_of_backDoor {X Y Z : Finset V} (v : ∀ u, α u)
    (hbd : G.BackDoor ↑X ↑Y ↑Z) (hYZ : Disjoint Y Z)
    (hpos : ∀ c : ∀ u, α u, (∀ u ∈ X, c u = v u) → 0 < M.dist.margAt Z c →
      0 < M.dist.margAt (X ∪ Z) c) :
    M.effect X v Y v = ∑ c ∈ FiniteDist.agreeOn Zᶜ v,
      M.dist.margAt (Y ∪ X ∪ Z) c / M.dist.margAt (X ∪ Z) c * M.dist.margAt Z c :=
  M.backdoor_adjustment v (disjoint_left_of_backDoor hbd) (disjoint_of_backDoor hbd) hYZ
    (fun u hu => hbd.1 u (mem_coe.2 hu)) hbd.2 hpos

/-- The configurations that agree with `v` on every coordinate: only `v` itself. -/
theorem agreeOn_compl_empty (v : ∀ u, α u) :
    FiniteDist.agreeOn (∅ : Finset V)ᶜ v = {v} := by
  ext c
  simp [funext_iff]

/-- **Adjustment for the parents of a single treatment**, as a corollary of the back-door
adjustment: the parents of `x` satisfy the back-door criterion relative to `({x}, Y)` for every
`Y` not containing `x` (`Digraph.IsAcyclic.backDoor_parents`). With `Y` disjoint from the
parents, `P(y | do(x)) = ∑_{pa} P(y | x, pa) P(pa)` under the positivity
`P(pa) > 0 → P(x, pa) > 0`. -/
theorem effect_eq_sum_parents (x : V) {Y : Finset V} (v : ∀ u, α u) (hxY : x ∉ Y)
    (hYpa : Disjoint Y (G.parentsFinset x))
    (hpos : ∀ c : ∀ u, α u, (∀ u ∈ ({x} : Finset V), c u = v u) →
      0 < M.dist.margAt (G.parentsFinset x) c → 0 < M.dist.margAt ({x} ∪ G.parentsFinset x) c) :
    M.effect {x} v Y v = ∑ c ∈ FiniteDist.agreeOn (G.parentsFinset x)ᶜ v,
      M.dist.margAt (Y ∪ {x} ∪ G.parentsFinset x) c / M.dist.margAt ({x} ∪ G.parentsFinset x) c *
        M.dist.margAt (G.parentsFinset x) c := by
  refine M.effect_eq_sum_of_backDoor v ?_ hYpa hpos
  rw [coe_singleton, Digraph.coe_parentsFinset]
  refine ⟨fun z hz ⟨s, hs, hsz⟩ => ?_, Digraph.dSep_iff_forall_singleton.2 fun a ha y hy => ?_⟩
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    exact M.acyclic s (Relation.TransGen.tail' hsz hz)
  · rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact (M.acyclic.backDoor_parents (y := y) fun h => hxY (by rwa [h])).2

/-- **No adjustment for a treatment without parents**, as a corollary of the back-door
adjustment: if no vertex of `X` has a parent, the empty set satisfies the back-door criterion
(`Digraph.backDoor_empty_of_parents_eq_empty`), and for `Y` disjoint from `X` with
`P(x) > 0`, `P(y | do(x)) = P(y, x) / P(x) = P(y | x)`. -/
theorem effect_eq_div_of_parents_eq_empty {X Y : Finset V} (v : ∀ u, α u)
    (hX : ∀ x ∈ X, G.parents x = ∅) (hXY : Disjoint X Y) (hpos : 0 < M.dist.margAt X v) :
    M.effect X v Y v = M.dist.margAt (Y ∪ X) v / M.dist.margAt X v := by
  have hbd : G.BackDoor ↑X ↑Y ↑(∅ : Finset V) := by
    rw [coe_empty]
    exact Digraph.backDoor_empty_of_parents_eq_empty hX (disjoint_coe.2 hXY)
  rw [M.effect_eq_sum_of_backDoor v hbd (disjoint_empty_right Y) fun c hc _ => by
      rw [union_empty, M.dist.margAt_congr X hc]; exact hpos,
    agreeOn_compl_empty, sum_singleton]
  simp only [union_empty, FiniteDist.margAt_empty, mul_one]

/-- **Identifiability by back-door adjustment** (Pearl 2009, Theorem 3.3.2): if `Z` satisfies
the back-door criterion relative to `(X, Y)` and `Y` is disjoint from `Z`, the effect
`P(y | do(x))` is identifiable from the marginal law of any observed set `O ⊇ X ∪ Y ∪ Z`, within
the class of models on `G` satisfying the positivity `P(z) > 0 → P(x, z) > 0`. All other
vertices may be latent. -/
theorem identifiableFrom_effect_of_backDoor {X Y Z O : Finset V} (v : ∀ u, α u)
    (hbd : G.BackDoor ↑X ↑Y ↑Z) (hYZ : Disjoint Y Z) (hO : X ∪ Y ∪ Z ⊆ O) :
    IdentifiableFrom {m : Model G α | ∀ c : ∀ u, α u, (∀ u ∈ X, c u = v u) →
        0 < m.scm.dist.margAt Z c → 0 < m.scm.dist.margAt (X ∪ Z) c}
      O (fun m => m.scm.effect X v Y v) := by
  intro m hm m' hm' hobs
  simp only at hobs ⊢
  rw [m.scm.effect_eq_sum_of_backDoor v hbd hYZ hm, m'.scm.effect_eq_sum_of_backDoor v hbd hYZ hm']
  have hsub : ∀ {S : Finset V}, S ⊆ X ∪ Y ∪ Z → ∀ c,
      m.scm.dist.margAt S c = m'.scm.dist.margAt S c :=
    fun hS c => FiniteDist.margAt_eq_of_marginal_eq hobs (hS.trans hO) c
  refine sum_congr rfl fun c _ => ?_
  rw [hsub (fun u hu => by simp only [mem_union] at hu ⊢; tauto) c,
    hsub (fun u hu => by simp only [mem_union] at hu ⊢; tauto) c,
    hsub (fun u hu => by simp only [mem_union] at hu ⊢; tauto) c]

/-- **Two admissible sets give the same adjustment value** (Pearl 2009, section 11.3.3,
equation (11.8), p. 345: two sets that both satisfy the back-door criterion are c-equivalent).
If `Z₁` and `Z₂` both satisfy the back-door criterion relative to `(X, Y)`, are disjoint from
`Y`, and each satisfies the positivity of the back-door adjustment, then
`∑_{z₁} P(y | x, z₁) P(z₁) = ∑_{z₂} P(y | x, z₂) P(z₂)`: both equal `P(y | do(x))`. -/
theorem adjustment_eq_of_backDoor {X Y Z₁ Z₂ : Finset V} (v : ∀ u, α u)
    (h₁ : G.BackDoor ↑X ↑Y ↑Z₁) (h₂ : G.BackDoor ↑X ↑Y ↑Z₂) (hY₁ : Disjoint Y Z₁)
    (hY₂ : Disjoint Y Z₂)
    (hpos₁ : ∀ c : ∀ u, α u, (∀ u ∈ X, c u = v u) → 0 < M.dist.margAt Z₁ c →
      0 < M.dist.margAt (X ∪ Z₁) c)
    (hpos₂ : ∀ c : ∀ u, α u, (∀ u ∈ X, c u = v u) → 0 < M.dist.margAt Z₂ c →
      0 < M.dist.margAt (X ∪ Z₂) c) :
    ∑ c ∈ FiniteDist.agreeOn Z₁ᶜ v,
        M.dist.margAt (Y ∪ X ∪ Z₁) c / M.dist.margAt (X ∪ Z₁) c * M.dist.margAt Z₁ c =
      ∑ c ∈ FiniteDist.agreeOn Z₂ᶜ v,
        M.dist.margAt (Y ∪ X ∪ Z₂) c / M.dist.margAt (X ∪ Z₂) c * M.dist.margAt Z₂ c := by
  rw [← M.effect_eq_sum_of_backDoor v h₁ hY₁ hpos₁, M.effect_eq_sum_of_backDoor v h₂ hY₂ hpos₂]

end SCM

/-! ### Adjustment for an inadmissible set -/

namespace SCM.BowExample

open DoCalculusCounterexamples

/-- **Adjustment for an inadmissible set gives a wrong value.** In the bow graph (a latent common
cause `U = 0` of `X = 1` and `Y = 2`, and the edge `X → Y`), the empty set does not satisfy the
back-door criterion relative to `(X, Y)`. In model A, where `P(X = true) = 1/2 > 0`, adjusting
for the empty set gives `P(Y = true | X = true) = 3/4`, while the effect
`P(Y = true | do(X = true))` is `1/2`. (Adjusting for the latent `U` would be admissible.) -/
theorem adjustment_empty_ne_effect :
    ¬ bow.BackDoor ↑({1} : Finset (Fin 3)) ↑({2} : Finset (Fin 3)) ↑(∅ : Finset (Fin 3)) ∧
      0 < modelA.dist.margAt ({1} ∪ ∅) treat ∧
      ∑ c ∈ FiniteDist.agreeOn (∅ : Finset (Fin 3))ᶜ treat,
        modelA.dist.margAt ({2} ∪ {1} ∪ ∅) c / modelA.dist.margAt ({1} ∪ ∅) c *
          modelA.dist.margAt ∅ c = 3 / 4 ∧
      modelA.effect {1} treat {2} treat = 1 / 2 := by
  refine ⟨?_, ?_, ?_, modelA_effect⟩
  · rw [coe_singleton, coe_singleton, coe_empty]
    decide +kernel
  · rw [union_empty, modelA_margAt_one]
    norm_num
  · rw [agreeOn_compl_empty, sum_singleton]
    simp only [union_empty, FiniteDist.margAt_empty, mul_one]
    rw [modelA_margAt_two_one, modelA_margAt_one]
    norm_num

end SCM.BowExample

end CausalInference

/-! ### The front-door criterion: consequences used below -/

namespace Digraph.FrontDoor

open Relation

variable {V : Type*} {G : Digraph V} {X Y Z : Set V}

/-- Condition (ii) of the front-door criterion makes the treatment and the mediator sets
disjoint. -/
theorem disjoint_XZ (h : G.FrontDoor X Y Z) : Disjoint X Z :=
  Set.disjoint_left.2 fun _ hx hz => (h.2.1.inter_subset ⟨hx, hz⟩ : _ ∈ (∅ : Set V))

/-- The front-door criterion makes the mediator and the outcome sets disjoint. -/
theorem disjoint_ZY (h : G.FrontDoor X Y Z) : Disjoint Z Y :=
  Set.disjoint_left.2 fun _ hz hy =>
    Set.disjoint_left.1 h.disjoint_XZ (h.2.2.inter_subset ⟨hz, hy⟩) hz

/-- The front-door criterion makes the treatment and the outcome sets disjoint. -/
theorem disjoint_XY (h : G.FrontDoor X Y Z) : Disjoint X Y :=
  Set.disjoint_left.2 fun _ hx hy =>
    Set.disjoint_left.1 h.disjoint_XZ hx (h.1.inter_subset ⟨hx, hy⟩)

/-- Under the front-door criterion no outcome vertex is a descendant of a treatment vertex once
the edges into the mediators are removed: such a directed path would avoid `Z`, against
condition (i). -/
theorem notMem_descendantsOf_deleteIncoming (h : G.FrontDoor X Y Z) {u : V} (hu : u ∈ Y) :
    u ∉ (G.deleteIncoming Z).descendantsOf X := by
  rintro ⟨s, hs, hsu⟩
  have hsZ : s ∉ Z := Set.disjoint_left.1 h.disjoint_XZ hs
  exact h.1 s hs u hu hsZ (reflTransGen_restrict_of_deleteIncoming hsu hsZ subset_rfl).2

end Digraph.FrontDoor

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-! ### The effect of treatment on the treated -/

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
/-- For a single treatment `t`, the auxiliary model of Rule 2, `M.rule2Model ∅ {t} v` (a model on
`G` with the edges out of `t` removed), computes at every noise value the counterfactual value
`V_{t := v t}` of every vertex other than `t`. -/
theorem solve_rule2Model_singleton_of_ne {t : V} (v : ∀ u, α u) (e : ∀ u, ε u) {w : V}
    (hw : w ≠ t) : (M.rule2Model ∅ {t} v).solve e w = (M.intervene {t} v).solve e w := by
  have hov := congrFun (M.override_solve_rule2Model (X := ∅) (Z := {t}) (v := v) e) w
  have key : ∀ X X' : Finset V, X = X' →
      (M.intervene X v).solve e w = (M.intervene X' v).solve e w := by
    rintro X X' rfl
    rfl
  rw [key _ _ (empty_union {t})] at hov
  simpa [hw] using hov

omit [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
/-- For a single treatment `t`, the auxiliary model of Rule 2, `M.rule2Model ∅ {t} v`, computes
at every noise value the factual value of `t`. -/
theorem solve_rule2Model_singleton_self (t : V) (v : ∀ u, α u) (e : ∀ u, ε u) :
    (M.rule2Model ∅ {t} v).solve e t = M.solve e t := by
  rw [(M.rule2Model ∅ {t} v).solve_eq e t, M.rule2Model_f_restrict_of_notMem (notMem_empty t),
    M.solve_eq e t]
  congr 1
  funext p
  have hpt := Digraph.mem_parentsFinset.1 p.2
  have hp : (p : V) ≠ t := fun h => M.acyclic.irrefl t (by rwa [h] at hpt)
  simp only [Finset.restrict, mem_singleton, hp, ite_false]
  rw [M.solve_rule2Model_singleton_of_ne v e hp]
  refine M.solve_intervene_of_notMem_descendantsOf e fun h => ?_
  obtain ⟨s, hs, hsp⟩ := Digraph.mem_descendantsOf.1 h
  rw [coe_singleton, Set.mem_singleton_iff] at hs
  subst hs
  exact M.acyclic s (Relation.TransGen.tail' hsp hpt)

/-- For a single treatment `t`, the auxiliary model of Rule 2, `M.rule2Model ∅ {t} v`, carries
the factual treatment, the counterfactual outcomes `Y_{t := v t}` and the factual covariates `Z`
(nondescendants of `t`): its marginal on `Y ∪ {t} ∪ Z` at `c` is the probability that
`X = c t`, `Y_x = c` on `Y` and `Z = c` on `Z`. -/
theorem margAt_rule2Model_ett (t : V) {Y Z : Finset V} (v c : ∀ u, α u) (htY : t ∉ Y)
    (htZ : t ∉ Z) (hZ : ∀ w ∈ Z, w ∉ G.descendantsOf ↑({t} : Finset V)) :
    (M.rule2Model ∅ {t} v).dist.margAt (Y ∪ {t} ∪ Z) c =
      M.noiseDist.probOf (fun e => M.solve e t = c t ∧
        (∀ w ∈ Y, (M.intervene {t} v).solve e w = c w) ∧ ∀ w ∈ Z, M.solve e w = c w) := by
  rw [margAt_dist]
  refine FiniteDist.probOf_congr _ fun e => ?_
  have hY : ∀ w ∈ Y, (M.rule2Model ∅ {t} v).solve e w = (M.intervene {t} v).solve e w :=
    fun w hw => M.solve_rule2Model_singleton_of_ne v e (fun h : w = t => htY (h ▸ hw))
  have hZ' : ∀ w ∈ Z, (M.rule2Model ∅ {t} v).solve e w = M.solve e w := fun w hw => by
    rw [M.solve_rule2Model_singleton_of_ne v e (fun h : w = t => htZ (h ▸ hw))]
    exact M.solve_intervene_of_notMem_descendantsOf e (hZ w hw)
  simp only [forall_mem_union, mem_singleton, forall_eq, M.solve_rule2Model_singleton_self]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h2, fun w hw => (hY w hw).symm.trans (h1 w hw),
      fun w hw => (hZ' w hw).symm.trans (h3 w hw)⟩
  · rintro ⟨h2, h1, h3⟩
    exact ⟨⟨fun w hw => (hY w hw).trans (h1 w hw), h2⟩,
      fun w hw => (hZ' w hw).trans (h3 w hw)⟩

/-- **The per-stratum identity for the effect of treatment on the treated**, division-free
(Pearl 2009, section 11.3.2, p. 344). Let `Z` satisfy the back-door criterion relative to a single
treatment `t` and the outcomes `Y`. Then at every configuration `c`,
with `x = v t`, `x' = c t`, and `y`, `z` the values of `c` on `Y` and `Z`,
`P(Y_x = y, x', z) * P(x, z) = P(y, x, z) * P(x', z)`, where `P(x, z)` and `P(y, x, z)` are
read off `c` with `t` set to `x`. No positivity is needed. -/
theorem ett_stratum (t : V) {Y Z : Finset V} (v c : ∀ u, α u)
    (hbd : G.BackDoor ↑({t} : Finset V) ↑Y ↑Z) :
    M.noiseDist.probOf (fun e => M.solve e t = c t ∧
        (∀ w ∈ Y, (M.intervene {t} v).solve e w = c w) ∧ ∀ w ∈ Z, M.solve e w = c w) *
        M.dist.margAt ({t} ∪ Z) (Function.update c t (v t)) =
      M.dist.margAt (Y ∪ {t} ∪ Z) (Function.update c t (v t)) * M.dist.margAt ({t} ∪ Z) c := by
  have htZ : t ∉ Z := disjoint_left.1 (disjoint_of_backDoor hbd) (mem_singleton_self t)
  have htY : t ∉ Y := disjoint_left.1 (disjoint_left_of_backDoor hbd) (mem_singleton_self t)
  have hZd : ∀ w ∈ Z, w ∉ G.descendantsOf ↑({t} : Finset V) := fun w hw => hbd.1 w (mem_coe.2 hw)
  have hZnd : ∀ e, ∀ w ∈ Z, (M.intervene {t} v).solve e w = M.solve e w := fun e w hw =>
    M.solve_intervene_of_notMem_descendantsOf e (hZd w hw)
  have hne : ∀ {w}, w ∈ Y ∪ Z → w ≠ t := fun hw h => by
    subst h
    rcases mem_union.1 hw with h | h
    · exact htY h
    · exact htZ h
  rw [← M.margAt_rule2Model_ett t v c htY htZ hZd]
  -- the global Markov property of the auxiliary model
  have hsep : ((G.deleteIncoming ↑(∅ : Finset V)).deleteOutgoing ↑({t} : Finset V)).DSep
      ↑Y ↑({t} : Finset V) ↑Z := by
    simpa using hbd.2.symm
  have hci := (M.rule2Model ∅ {t} v).factorizes.condIndep_of_dSep
    (M.rule2Model ∅ {t} v).acyclic hsep
  -- marginals of the auxiliary model
  have hRZ : ∀ c, (M.rule2Model ∅ {t} v).dist.margAt Z c = M.dist.margAt Z c := fun c => by
    rw [margAt_dist, margAt_dist]
    refine FiniteDist.probOf_congr _ fun e => forall₂_congr fun w hw => ?_
    rw [M.solve_rule2Model_singleton_of_ne v e (hne (mem_union_right _ hw)), hZnd e w hw]
  have hRYZ : ∀ c, (M.rule2Model ∅ {t} v).dist.margAt (Y ∪ Z) c =
      (M.intervene {t} v).dist.margAt (Y ∪ Z) c := fun c => by
    rw [margAt_dist, margAt_dist]
    refine FiniteDist.probOf_congr _ fun e => forall₂_congr fun w hw => ?_
    rw [M.solve_rule2Model_singleton_of_ne v e (hne hw)]
  have hRtZ : ∀ c, (M.rule2Model ∅ {t} v).dist.margAt ({t} ∪ Z) c =
      M.dist.margAt ({t} ∪ Z) c := fun c => by
    rw [margAt_dist, margAt_dist]
    refine FiniteDist.probOf_congr _ fun e => forall₂_congr fun w hw => ?_
    by_cases h : w = t
    · subst h
      rw [M.solve_rule2Model_singleton_self]
    · rw [M.solve_rule2Model_singleton_of_ne v e h,
        hZnd e w ((mem_union.1 hw).resolve_left fun h' => h (mem_singleton.1 h'))]
  have hm := hci.margAt_mul c
  rw [hRZ, hRYZ, hRtZ] at hm
  -- the per-stratum back-door identity at the treatment value
  have st := M.backdoor_stratum hbd (Function.update c t (v t))
  rw [M.intervene_congr (x' := v) fun u hu => by rw [mem_singleton.1 hu, Function.update_self],
    (M.intervene {t} v).dist.margAt_congr (Y ∪ Z) fun u hu => Function.update_of_ne (hne hu) _ _,
    M.dist.margAt_congr Z fun u hu => Function.update_of_ne (hne (mem_union_right _ hu)) _ _] at st
  rcases (M.dist.margAt_nonneg Z c).eq_or_lt with h0 | hz
  · have h1 : (M.rule2Model ∅ {t} v).dist.margAt (Y ∪ {t} ∪ Z) c = 0 :=
      le_antisymm ((FiniteDist.margAt_anti _ subset_union_right c).trans
        (by rw [hRZ, ← h0])) (FiniteDist.margAt_nonneg _ _ _)
    have h2 : M.dist.margAt ({t} ∪ Z) c = 0 :=
      le_antisymm ((FiniteDist.margAt_anti _ subset_union_right c).trans h0.ge)
        (FiniteDist.margAt_nonneg _ _ _)
    rw [h1, h2, mul_zero, zero_mul]
  · exact mul_right_cancel₀ hz.ne' (by
      linear_combination M.dist.margAt ({t} ∪ Z) (Function.update c t (v t)) * hm +
        M.dist.margAt ({t} ∪ Z) c * st)

/-- **The effect of treatment on the treated by back-door adjustment**, joint form, with overlap
on the support of the treated group only (Pearl 2009, section 11.3.2, p. 344). Let `Z` satisfy
the back-door criterion relative to a single treatment `t` and the outcomes `Y`, with `Y`
disjoint from `Z`, and assume the overlap `P(x', z) > 0 → P(x, z) > 0` for the factual
treatment value `x' = c₀ t` and the treatment value `x = v t`. Then the probability that the
factual treatment is `x'` and the counterfactual outcome `Y_x` is `y` (the values of `c₀` on `Y`)
is `P(x', Y_x = y) = ∑_z P(y | x, z) P(x', z)`, where `P(y | x, z)` is read off the configuration
`c` with `t` set to `x`. The sum runs over the configurations that agree with `c₀` outside `Z`;
strata with `P(x', z) = 0` contribute zero on both sides. The per-stratum identity is
`SCM.ett_stratum`. -/
theorem ett_joint_eq_sum_of_backDoor_of_overlap (t : V) {Y Z : Finset V} (v c₀ : ∀ u, α u)
    (hbd : G.BackDoor ↑({t} : Finset V) ↑Y ↑Z) (hYZ : Disjoint Y Z)
    (hpos : ∀ c : ∀ u, α u, c t = c₀ t → 0 < M.dist.margAt ({t} ∪ Z) c →
      0 < M.dist.margAt ({t} ∪ Z) (Function.update c t (v t))) :
    M.noiseDist.probOf (fun e => M.solve e t = c₀ t ∧
        ∀ w ∈ Y, (M.intervene {t} v).solve e w = c₀ w) =
      ∑ c ∈ FiniteDist.agreeOn Zᶜ c₀,
        M.dist.margAt (Y ∪ {t} ∪ Z) (Function.update c t (v t)) /
          M.dist.margAt ({t} ∪ Z) (Function.update c t (v t)) * M.dist.margAt ({t} ∪ Z) c := by
  have htZ : t ∉ Z := disjoint_left.1 (disjoint_of_backDoor hbd) (mem_singleton_self t)
  have htY : t ∉ Y := disjoint_left.1 (disjoint_left_of_backDoor hbd) (mem_singleton_self t)
  have hZd : ∀ w ∈ Z, w ∉ G.descendantsOf ↑({t} : Finset V) := fun w hw => hbd.1 w (mem_coe.2 hw)
  have hL := M.margAt_rule2Model_ett t v c₀ htY (notMem_empty t) (Z := ∅)
    (fun w hw => absurd hw (notMem_empty w))
  simp only [union_empty, notMem_empty, IsEmpty.forall_iff, implies_true, and_true] at hL
  have hdisj : Disjoint (Y ∪ {t}) Z := disjoint_union_left.2 ⟨hYZ, disjoint_singleton_left.2 htZ⟩
  rw [← hL, FiniteDist.margAt_eq_sum_margAt _ (subset_union_left (s₂ := Z)),
    union_sdiff_cancel_left hdisj]
  refine sum_congr rfl fun c hc => ?_
  rw [M.margAt_rule2Model_ett t v c htY htZ hZd]
  have hct : c t = c₀ t := FiniteDist.mem_agreeOn.1 hc t (mem_compl.2 htZ)
  rcases (M.dist.margAt_nonneg ({t} ∪ Z) c).eq_or_lt with h0 | hp
  · have h1 : M.noiseDist.probOf (fun e => M.solve e t = c t ∧
        (∀ w ∈ Y, (M.intervene {t} v).solve e w = c w) ∧ ∀ w ∈ Z, M.solve e w = c w) = 0 := by
      refine le_antisymm ((FiniteDist.probOf_mono _ fun e h => ?_).trans_eq
        ((margAt_dist M ({t} ∪ Z) c).symm.trans h0.symm)) (FiniteDist.probOf_nonneg _)
      rw [forall_mem_union]
      simpa using ⟨h.1, h.2.2⟩
    rw [h1, ← h0, mul_zero]
  · have hx := hpos c hct hp
    rw [div_mul_eq_mul_div, eq_div_iff hx.ne', M.ett_stratum t v c hbd]

/-- **The effect of treatment on the treated by back-door adjustment**, joint form under the
stronger positivity `P(z) > 0 → P(x, z) > 0` at the treatment value `x = v t` (Pearl 2009,
section 11.3.2, p. 344): a corollary of `SCM.ett_joint_eq_sum_of_backDoor_of_overlap`, whose
overlap hypothesis `P(x', z) > 0 → P(x, z) > 0` it implies. Then
`P(x', Y_x = y) = ∑_z P(y | x, z) P(x', z)` for `x' = c₀ t`.

The proof of the underlying stratum identity (`SCM.ett_stratum`) uses the auxiliary model of
Rule 2 for the treatment (`SCM.margAt_rule2Model_ett`): it carries the factual treatment and the
counterfactual outcome, it is a model on the graph with the edges out of `t` removed, and there
the back-door criterion is the d-separation `Y ⫫ t | Z`; its global Markov property gives
`Y_x ⫫ X | Z`. -/
theorem ett_joint_eq_sum_of_backDoor (t : V) {Y Z : Finset V} (v c₀ : ∀ u, α u)
    (hbd : G.BackDoor ↑({t} : Finset V) ↑Y ↑Z) (hYZ : Disjoint Y Z)
    (hpos : ∀ c : ∀ u, α u, 0 < M.dist.margAt Z c →
      0 < M.dist.margAt ({t} ∪ Z) (Function.update c t (v t))) :
    M.noiseDist.probOf (fun e => M.solve e t = c₀ t ∧
        ∀ w ∈ Y, (M.intervene {t} v).solve e w = c₀ w) =
      ∑ c ∈ FiniteDist.agreeOn Zᶜ c₀,
        M.dist.margAt (Y ∪ {t} ∪ Z) (Function.update c t (v t)) /
          M.dist.margAt ({t} ∪ Z) (Function.update c t (v t)) * M.dist.margAt ({t} ∪ Z) c :=
  M.ett_joint_eq_sum_of_backDoor_of_overlap t v c₀ hbd hYZ fun c _ hc =>
    hpos c (hc.trans_le (M.dist.margAt_anti subset_union_right c))

/-- **The effect of treatment on the treated by back-door adjustment** (Pearl 2009,
section 11.3.2, p. 344): under the hypotheses of `SCM.ett_joint_eq_sum_of_backDoor_of_overlap`
(overlap `P(x', z) > 0 → P(x, z) > 0` on the support of the treated group `x' = c₀ t` only) and
`P(x') > 0`, the counterfactual probability `P(Y_x = y | X = x')` (abduction, action and
prediction, `SCM.counterfactualProb`) is `∑_z P(y | x, z) P(z | x')`, with
`P(z | x') = P(x', z) / P(x')`. -/
theorem ett_eq_sum_of_backDoor_of_overlap (t : V) {Y Z : Finset V} (v c₀ : ∀ u, α u)
    (hbd : G.BackDoor ↑({t} : Finset V) ↑Y ↑Z) (hYZ : Disjoint Y Z)
    (hpos : ∀ c : ∀ u, α u, c t = c₀ t → 0 < M.dist.margAt ({t} ∪ Z) c →
      0 < M.dist.margAt ({t} ∪ Z) (Function.update c t (v t)))
    (hx' : 0 < M.dist.probOf (fun w => w t = c₀ t)) :
    M.counterfactualProb (fun w => w t = c₀ t) hx' {t} v (fun w => ∀ u ∈ Y, w u = c₀ u) =
      ∑ c ∈ FiniteDist.agreeOn Zᶜ c₀,
        M.dist.margAt (Y ∪ {t} ∪ Z) (Function.update c t (v t)) /
          M.dist.margAt ({t} ∪ Z) (Function.update c t (v t)) *
            (M.dist.margAt ({t} ∪ Z) c / M.dist.probOf (fun w => w t = c₀ t)) := by
  rw [counterfactualProb_eq, M.ett_joint_eq_sum_of_backDoor_of_overlap t v c₀ hbd hYZ hpos,
    sum_div]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_div_assoc]

/-- **The effect of treatment on the treated by back-door adjustment**, under the stronger
positivity `P(z) > 0 → P(x, z) > 0` and `P(x') > 0`: a corollary of
`SCM.ett_eq_sum_of_backDoor_of_overlap`. -/
theorem ett_eq_sum_of_backDoor (t : V) {Y Z : Finset V} (v c₀ : ∀ u, α u)
    (hbd : G.BackDoor ↑({t} : Finset V) ↑Y ↑Z) (hYZ : Disjoint Y Z)
    (hpos : ∀ c : ∀ u, α u, 0 < M.dist.margAt Z c →
      0 < M.dist.margAt ({t} ∪ Z) (Function.update c t (v t)))
    (hx' : 0 < M.dist.probOf (fun w => w t = c₀ t)) :
    M.counterfactualProb (fun w => w t = c₀ t) hx' {t} v (fun w => ∀ u ∈ Y, w u = c₀ u) =
      ∑ c ∈ FiniteDist.agreeOn Zᶜ c₀,
        M.dist.margAt (Y ∪ {t} ∪ Z) (Function.update c t (v t)) /
          M.dist.margAt ({t} ∪ Z) (Function.update c t (v t)) *
            (M.dist.margAt ({t} ∪ Z) c / M.dist.probOf (fun w => w t = c₀ t)) :=
  M.ett_eq_sum_of_backDoor_of_overlap t v c₀ hbd hYZ
    (fun c _ hc => hpos c (hc.trans_le (M.dist.margAt_anti subset_union_right c))) hx'

/-! ### Front-door adjustment -/

/-- The division-free identity behind the front-door formula. If `Z` satisfies the front-door
criterion relative to `(X, Y)`, then at every configuration `c`,
`P(y, z | do(x)) * P(x) = P(y | do(z)) * P(z, x)`, all values read off `c`. No positivity is
needed for this product identity. The divided form `P(y, z | do(x)) = P(z | x) P(y | do(z))`
is `SCM.frontdoor_stratum_div`, which needs `P(x) > 0`: without it the two sides can differ
(`SCM.CopyChainExample.frontdoor_stratum_div_ne`).

The proof follows Pearl (2009), section 3.4.3: Rule 2 gives `P(z | do(x)) = P(z | x)` (Task 1)
and `P(y | do(x), z) = P(y | do(x), do(z))`; the intervention on `X` is then removed because no
vertex of `Y` descends from `X` once the edges into `Z` are cut (in place of Rule 3). -/
theorem frontdoor_stratum {X Y Z : Finset V} (hfd : G.FrontDoor ↑X ↑Y ↑Z) (c : ∀ u, α u) :
    (M.intervene X c).dist.margAt (Y ∪ Z) c * M.dist.margAt X c =
      (M.intervene Z c).dist.margAt Y c * M.dist.margAt (Z ∪ X) c := by
  have hXZ : Disjoint X Z := disjoint_coe.1 hfd.disjoint_XZ
  have hZY : Disjoint Z Y := disjoint_coe.1 hfd.disjoint_ZY
  -- Task 1 (Rule 2): `P(z | do(x)) * P(x) = P(z, x)`
  have t1 := M.rule2 (X := ∅) (Y := Z) (Z := X) (W := ∅) c (disjoint_empty_left X) hXZ.symm
    (disjoint_empty_left X) (by simpa using hfd.2.1.symm)
  rw [M.dist_intervene_of_eq (empty_union X)] at t1
  simp only [dist_intervene_empty, union_empty, FiniteDist.margAt_empty, mul_one] at t1
  -- Rule 2: `P(y | do(x), do(z)) * P(z | do(x)) = P(y, z | do(x))`
  have t2 := M.rule2 (X := X) (Y := Y) (Z := Z) (W := ∅) c hXZ hZY.symm (disjoint_empty_left Z)
    (by rw [union_empty, Digraph.deleteIncoming_deleteOutgoing]
        exact hfd.2.2.symm.deleteIncoming)
  simp only [union_empty, FiniteDist.margAt_empty, mul_one] at t2
  -- the intervention on `X` does not reach `Y` once `Z` is fixed
  have t3 : (M.intervene (X ∪ Z) c).dist.margAt Y c = (M.intervene Z c).dist.margAt Y c := by
    rw [M.dist_intervene_of_eq (union_comm X Z),
      ← (M.intervene Z c).margAt_intervene_of_notMem_descendantsOf (X := X) (x := c)
        (fun u hu => hfd.notMem_descendantsOf_deleteIncoming hu) c,
      M.dist_intervene_intervene]
    simp only [ite_self]
  rw [← t2, ← t1, t3]
  ring

/-- The divided form of `SCM.frontdoor_stratum`: if `Z` satisfies the front-door criterion
relative to `(X, Y)` and `P(x) > 0`, then `P(y, z | do(x)) = P(z | x) P(y | do(z))`, with
`P(z | x) = P(z, x) / P(x)`, all values read off `c`. -/
theorem frontdoor_stratum_div {X Y Z : Finset V} (hfd : G.FrontDoor ↑X ↑Y ↑Z) (c : ∀ u, α u)
    (hx : 0 < M.dist.margAt X c) :
    (M.intervene X c).dist.margAt (Y ∪ Z) c =
      M.dist.margAt (Z ∪ X) c / M.dist.margAt X c * (M.intervene Z c).dist.margAt Y c := by
  rw [div_mul_eq_mul_div, eq_div_iff hx.ne', M.frontdoor_stratum hfd c, mul_comm]

/-- **Front-door adjustment** (Pearl 2009, Theorem 3.3.4, equation (3.29)), for any graph and
any sets `X`, `Y`, `Z` such that `Z` satisfies the front-door criterion relative to `(X, Y)`
(`Digraph.FrontDoor`). If the law of `(X, Z)` is strictly positive (Pearl's `P(x, z) > 0`), then
`P(y | do(x)) = ∑_z P(z | x) ∑_x' P(y | x', z) P(x')`, with `P(z | x) = P(z, x) / P(x)` and
`P(y | x', z) = P(y, z, x') / P(z, x')`. The outer sum runs over the configurations that agree
with `v` outside `Z`, the inner one over those that agree with `c` outside `X`. Only marginals
on subsets of `X ∪ Y ∪ Z` appear on the right; every other vertex may be latent.

This generalizes `SCM.FrontDoorExample.frontdoor_formula`, which treats the canonical
four-vertex graph. -/
theorem effect_eq_sum_of_frontDoor {X Y Z : Finset V} (v : ∀ u, α u)
    (hfd : G.FrontDoor ↑X ↑Y ↑Z) (hpos : ∀ c : ∀ u, α u, 0 < M.dist.margAt (X ∪ Z) c) :
    M.effect X v Y v = ∑ c ∈ FiniteDist.agreeOn Zᶜ v,
      M.dist.margAt (Z ∪ X) c / M.dist.margAt X c *
        ∑ d ∈ FiniteDist.agreeOn Xᶜ c,
          M.dist.margAt (Y ∪ Z ∪ X) d / M.dist.margAt (Z ∪ X) d * M.dist.margAt X d := by
  have hXZ : Disjoint X Z := disjoint_coe.1 hfd.disjoint_XZ
  have hZY : Disjoint Z Y := disjoint_coe.1 hfd.disjoint_ZY
  have hXY : Disjoint X Y := disjoint_coe.1 hfd.disjoint_XY
  rw [effect, FiniteDist.margAt_eq_sum_margAt _ (subset_union_left (s₂ := Z)),
    union_sdiff_cancel_left hZY.symm]
  refine sum_congr rfl fun c hc => ?_
  have hcX : ∀ u ∈ X, v u = c u := fun u hu =>
    ((FiniteDist.mem_agreeOn.1 hc) u (mem_compl.2 (disjoint_left.1 hXZ hu))).symm
  rw [M.intervene_congr hcX]
  -- the back-door adjustment for `P(y | do(z))`, adjusting for `X`
  have bd := M.backdoor_adjustment (X := Z) (Y := Y) (Z := X) c hZY hXZ.symm hXY.symm
    (fun u hu => hfd.notMem_descendantsOf_mediator hu) hfd.2.2 fun d _ _ => by
      rw [union_comm]
      exact hpos d
  rw [effect] at bd
  have hx : 0 < M.dist.margAt X c := (hpos c).trans_le (M.dist.margAt_anti subset_union_left c)
  rw [← bd, M.frontdoor_stratum_div hfd c hx]

/-- **Identifiability by front-door adjustment** (Pearl 2009, Theorem 3.3.4): if `Z` satisfies
the front-door criterion relative to `(X, Y)`, the effect `P(y | do(x))` is identifiable from the
marginal law of any observed set `O ⊇ X ∪ Y ∪ Z`, within the class of models on `G` in which
the law of `(X, Z)` is strictly positive. All other vertices may be latent. -/
theorem identifiableFrom_effect_of_frontDoor {X Y Z O : Finset V} (v : ∀ u, α u)
    (hfd : G.FrontDoor ↑X ↑Y ↑Z) (hO : X ∪ Y ∪ Z ⊆ O) :
    IdentifiableFrom {m : Model G α | ∀ c : ∀ u, α u, 0 < m.scm.dist.margAt (X ∪ Z) c}
      O (fun m => m.scm.effect X v Y v) := by
  intro m hm m' hm' hobs
  simp only at hobs ⊢
  rw [m.scm.effect_eq_sum_of_frontDoor v hfd hm, m'.scm.effect_eq_sum_of_frontDoor v hfd hm']
  have hsub : ∀ {S : Finset V}, S ⊆ X ∪ Y ∪ Z → ∀ c,
      m.scm.dist.margAt S c = m'.scm.dist.margAt S c :=
    fun hS c => FiniteDist.margAt_eq_of_marginal_eq hobs (hS.trans hO) c
  have h1 : ∀ c, m.scm.dist.margAt (Z ∪ X) c = m'.scm.dist.margAt (Z ∪ X) c :=
    hsub (fun u hu => by simp only [mem_union] at hu ⊢; tauto)
  have h2 : ∀ c, m.scm.dist.margAt X c = m'.scm.dist.margAt X c :=
    hsub (fun u hu => by simp only [mem_union] at hu ⊢; tauto)
  have h3 : ∀ c, m.scm.dist.margAt (Y ∪ Z ∪ X) c = m'.scm.dist.margAt (Y ∪ Z ∪ X) c :=
    hsub (fun u hu => by simp only [mem_union] at hu ⊢; tauto)
  simp only [h1, h2, h3]

end SCM

/-! ### The divided front-door stratum needs `P(x) > 0` -/

namespace SCM.CopyChainExample

open GraphExamples

open Rule3PositivityExample (allTrue)

/-- **The divided form of the front-door stratum needs `P(x) > 0`.** In
`SCM.CopyChainExample.model` (the chain `X = 0 → Z = 1 → Y = 2` with `X := false`, `Z := X`,
`Y := Z`), `Z = {1}` satisfies the front-door criterion relative to `(X, Y) = ({0}, {2})`. At
the all-`true` configuration, `P(y, z | do(x)) = 1` while `P(x) = 0`, so the right side
`P(z, x) / P(x) * P(y | do(z))` of `SCM.frontdoor_stratum_div` is `0 / 0 * P(y | do(z)) = 0`
in Lean. The product identity `SCM.frontdoor_stratum` holds (both sides are `0`). -/
theorem frontdoor_stratum_div_ne :
    chain.FrontDoor ↑({0} : Finset (Fin 3)) ↑({2} : Finset (Fin 3)) ↑({1} : Finset (Fin 3)) ∧
      model.dist.margAt {0} allTrue = 0 ∧
      (model.intervene {0} allTrue).dist.margAt ({2} ∪ {1}) allTrue = 1 ∧
      model.dist.margAt ({1} ∪ {0}) allTrue / model.dist.margAt {0} allTrue *
        (model.intervene {1} allTrue).dist.margAt {2} allTrue = 0 := by
  refine ⟨by decide, margAt_allTrue (by decide), intervene_margAt_allTrue _, ?_⟩
  rw [margAt_allTrue (by decide), zero_div, zero_mul]

end SCM.CopyChainExample

end CausalInference
