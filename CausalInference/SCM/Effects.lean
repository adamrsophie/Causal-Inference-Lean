/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Intervention
public import CausalInference.Basic.FiniteCondIndep
public import CausalInference.PartialIdentification.IdentifiedSet

/-!
# Causal effects, adjustment for direct causes, and identifiability

## Main definitions

* `SCM.effect M X x Y y`: the causal effect `P(Y = y | do(X := x))`, the marginal on `Y` of the
  distribution induced by the submodel of `do(X := x)` (Pearl 2009, Definition 3.2.1).
* `SCM.Model G α`: a finite Markovian structural causal model on `G` together with its noise
  types, so that models with different noise spaces form a single type.
* `SCM.IdentifiableFrom C O Q`: the query `Q` is identifiable within the class of models `C` from
  the marginal law of the observed vertices `O`; an instance of `PointIdentified` (Pearl 2009,
  Definitions 3.2.3 and 3.2.4).

## Main results

* `SCM.effect_congr`, `SCM.effect_eq_probOf_potentialResponse`,
  `SCM.effect_of_notMem_descendantsOf`: only the values of `x` on `X` matter; the effect is the
  probability `P_u(Y_x(u) = y)` of potential responses; an intervention does not affect
  non-descendants.
* `SCM.meanDo`, `SCM.averageCausalEffect`: the mean `E[g(V) | do(X := x)]` of a real outcome and
  the average causal effect, with `SCM.meanDo_eq_expect_potentialResponse` and
  `SCM.averageCausalEffect_eq_expect` (the mean of the unit-level effects).
* `SCM.probOf_and_parents_eq`: the kernel is the conditional law given the parents,
  `P(x_i = a, pa_i = z) = kernel i z a * P(pa_i = z)`.
* `SCM.effect_singleton_eq_sum` (**adjustment for direct causes**, Pearl 2009, Theorem 3.2.2):
  `P(y | do(x_i)) = ∑_{pa_i} P(y | x_i, pa_i) P(pa_i)`, under the positivity hypothesis that
  every parent configuration of positive probability gives `x_i` positive probability.
* `SCM.dist_intervene_eq_of_dist_eq`, `SCM.identifiableFrom_dist_intervene`,
  `SCM.identifiableFrom_effect` (Pearl 2009, Corollary 3.2.6): with every vertex observed and a
  strictly positive joint law, the interventional law of `do(X := x)` is identifiable for every
  set `X`; `SCM.identifiableFrom_effect_singleton` is the case of one vertex.
* `SCM.identifiableFrom_effect_singleton_of_subset` (Pearl 2009, Theorem 3.2.5, for one
  intervened vertex): the effect of `do(X_i := x_i)` on `Y` is identifiable from any observed set
  containing `{i} ∪ PA_i ∪ Y`, under overlap on the supported parent rows.
* `SCM.BowExample.not_identifiableFrom_effect` (Pearl 2009, Figure 3.7(a), the bow pattern):
  with a latent common cause `U` of `X` and `Y` and the edge `X → Y`, two models have the same
  strictly positive observed law of `(X, Y)` and different effects `P(Y = 1 | do(X = 1))`
  (`1/2` and `3/4`), so the effect is not identifiable.
  `SCM.BowExample.not_identifiableFrom_effect_of_all_observed`: the same two models show that
  without positivity the effect is not identifiable even with every vertex observed.
  `SCM.BowExample.not_identifiableFrom_effect_of_pos`: a second pair of models, with strictly
  positive joint law of all three vertices and every arrow active, and effects `1/2` and `5/8`.

The models of `SCM.Model G α` have fixed value types `α v` at every vertex, the latent ones
included; see `SCM.IdentifiableFrom` for what this means for the positive results.

Sources: Pearl (2009), *Causality*, 2nd edition, sections 3.2.1 to 3.2.4 and 3.5.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace SCM

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
  {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] {ε : V → Type*}
  [∀ v, Fintype (ε v)] (M : SCM G α ε)

/-- The causal effect `P(Y = y_Y | do(X := x_X))`: the probability, under the distribution induced
by the submodel of `do(X := x)`, that the vertices of `Y` take the values given by `y`. -/
noncomputable def effect (X : Finset V) (x : ∀ v, α v) (Y : Finset V) (y : ∀ v, α v) : ℝ :=
  (M.intervene X x).dist.margAt Y y

/-- The causal effect depends only on the values of `x` on `X`. -/
theorem effect_congr {X : Finset V} {x x' : ∀ v, α v} (h : ∀ v ∈ X, x v = x' v) (Y : Finset V)
    (y : ∀ v, α v) : M.effect X x Y y = M.effect X x' Y y := by
  rw [effect, effect, M.dist_intervene_congr h]

/-- **The causal effect is a probability of potential responses**:
`P(Y = y | do(X := x)) = P_u(Y_x(u) = y)`. -/
theorem effect_eq_probOf_potentialResponse (X : Finset V) (x : ∀ v, α v) (Y : Finset V)
    (y : ∀ v, α v) :
    M.effect X x Y y =
      M.noiseDist.probOf (fun u => ∀ v ∈ Y, M.potentialResponse X x u v = y v) := by
  rw [effect, margAt_dist, noiseDist_intervene]
  rfl

/-- **An intervention has no effect on non-descendants**: if no vertex of `Y` is a descendant of
`X`, then `P(Y = y | do(X := x)) = P(Y = y)`. -/
theorem effect_of_notMem_descendantsOf {X : Finset V} (x : ∀ v, α v) {Y : Finset V}
    (hY : ∀ v ∈ Y, v ∉ G.descendantsOf ↑X) (y : ∀ v, α v) :
    M.effect X x Y y = M.dist.margAt Y y :=
  M.margAt_intervene_of_notMem_descendantsOf hY y

/-! ### Means of real outcomes under interventions -/

/-- The **mean of a real outcome under `do(X := x)`**: the expectation `E[g(V) | do(X := x)]` of a
real function `g` of the configuration under the interventional distribution. -/
noncomputable def meanDo (X : Finset V) (x : ∀ v, α v) (g : (∀ v, α v) → ℝ) : ℝ :=
  (M.intervene X x).dist.expect g

/-- The mean under `do(X := x)` is the mean of the outcome at the potential response:
`E[g(V) | do(X := x)] = E_u[g(V_x(u))]`. -/
theorem meanDo_eq_expect_potentialResponse (X : Finset V) (x : ∀ v, α v)
    (g : (∀ v, α v) → ℝ) :
    M.meanDo X x g = M.noiseDist.expect (fun u => g (M.potentialResponse X x u)) := by
  rw [meanDo, dist, noiseDist_intervene, FiniteDist.expect_map]
  rfl

/-- The causal effect is the mean of the indicator of the outcome event. -/
theorem effect_eq_meanDo (X : Finset V) (x : ∀ v, α v) (Y : Finset V) (y : ∀ v, α v) :
    M.effect X x Y y = M.meanDo X x (fun w => if ∀ v ∈ Y, w v = y v then 1 else 0) := by
  rw [effect, FiniteDist.margAt_eq_probOf, meanDo, FiniteDist.probOf,
    FiniteDist.prob_eq_expect]
  simp only [mem_filter, mem_univ, true_and]

/-- The **average causal effect** of `do(X := x)` against `do(X := x')` on the real outcome `g`:
`E[g(V) | do(X := x)] - E[g(V) | do(X := x')]`. -/
noncomputable def averageCausalEffect (X : Finset V) (x x' : ∀ v, α v) (g : (∀ v, α v) → ℝ) :
    ℝ :=
  M.meanDo X x g - M.meanDo X x' g

/-- The average causal effect is the mean of the unit-level effects
`g(V_x(u)) - g(V_{x'}(u))`, computed at one shared noise value. -/
theorem averageCausalEffect_eq_expect (X : Finset V) (x x' : ∀ v, α v) (g : (∀ v, α v) → ℝ) :
    M.averageCausalEffect X x x' g = M.noiseDist.expect
      (fun u => g (M.potentialResponse X x u) - g (M.potentialResponse X x' u)) := by
  rw [averageCausalEffect, meanDo_eq_expect_potentialResponse,
    meanDo_eq_expect_potentialResponse]
  simp only [FiniteDist.expect, mul_sub, sum_sub_distrib]

omit [DecidableEq V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
include M in
/-- A configuration with prescribed values on the parents of `i` and at `i`. -/
theorem exists_restrict_parents_eq (i : V) (z : ∀ u : G.parentsFinset i, α u) (a : α i) :
    ∃ w : ∀ v, α v, (G.parentsFinset i).restrict w = z ∧ w i = a := by
  classical
  let w₀ : ∀ v, α v := M.solve fun v => Classical.choice (M.noise v).nonempty
  have hi : i ∉ G.parentsFinset i := fun h => M.acyclic.irrefl i (Digraph.mem_parentsFinset.1 h)
  refine ⟨Function.update (FiniteDist.override (G.parentsFinset i) z w₀) i a, ?_, by simp⟩
  funext p
  have hp : (p : V) ≠ i := fun h => hi (by have := p.2; rwa [h] at this)
  simp only [Finset.restrict, Function.update_of_ne hp]
  exact FiniteDist.override_of_mem z w₀ p.2

/-- The kernel of `i` is the conditional law of `i` given its parents:
`P(x_i = a, pa_i = z) = kernel i z a * P(pa_i = z)`. -/
theorem probOf_and_parents_eq (i : V) (z : ∀ u : G.parentsFinset i, α u) (a : α i) :
    M.dist.probOf (fun w => w i = a ∧ (G.parentsFinset i).restrict w = z) =
      M.kernel i z a * M.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) := by
  obtain ⟨w₁, hz, ha⟩ := M.exists_restrict_parents_eq i z a
  have h1 : M.dist.probOf (fun w => w i = a ∧ (G.parentsFinset i).restrict w = z) =
      M.dist.margAt (insert i (G.parentsFinset i)) w₁ := by
    rw [FiniteDist.margAt_eq_probOf]
    refine FiniteDist.probOf_congr _ fun w => ?_
    rw [← hz, ← ha, FiniteDist.restrict_eq_restrict_iff, forall_mem_insert]
  have h2 : M.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) =
      M.dist.margAt (G.parentsFinset i) w₁ := by
    rw [← hz]
    exact FiniteDist.probOf_restrict_eq_margAt₁ w₁
  rw [h1, h2, M.margAt_insert_parents, hz, ha]

/-- The parent configuration of `i` has the same law with or without an intervention on `i`. -/
theorem probOf_intervene_singleton_parents (i : V) (x : ∀ v, α v)
    (z : ∀ u : G.parentsFinset i, α u) :
    (M.intervene {i} x).dist.probOf (fun w => (G.parentsFinset i).restrict w = z) =
      M.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) := by
  rw [probOf_dist, probOf_dist, noiseDist_intervene]
  refine FiniteDist.probOf_congr _ fun u => ?_
  have : (G.parentsFinset i).restrict ((M.intervene {i} x).solve u) =
      (G.parentsFinset i).restrict (M.solve u) := by
    funext p
    refine M.solve_intervene_of_notMem_descendantsOf u fun h => ?_
    obtain ⟨s, hs, hsp⟩ := Digraph.mem_descendantsOf.1 h
    rw [coe_singleton, Set.mem_singleton_iff] at hs
    subst hs
    exact M.acyclic s (Relation.TransGen.tail' hsp (Digraph.mem_parentsFinset.1 p.2))
  rw [this]

/-- The key step of the adjustment formula: within the stratum `pa_i = z`, the interventional
mass of an event times the kernel `kernel i z (x i)` is the observational probability of the
event together with `x_i`. -/
theorem probOf_intervene_singleton_mul (i : V) (x : ∀ v, α v) (z : ∀ u : G.parentsFinset i, α u)
    (E : (∀ v, α v) → Prop) [DecidablePred E] :
    (M.intervene {i} x).dist.probOf (fun w => E w ∧ (G.parentsFinset i).restrict w = z) *
        M.kernel i z (x i) =
      M.dist.probOf (fun w => E w ∧ w i = x i ∧ (G.parentsFinset i).restrict w = z) := by
  unfold FiniteDist.probOf FiniteDist.prob
  rw [sum_mul, sum_filter, sum_filter]
  refine sum_congr rfl fun w _ => ?_
  rw [dist_intervene, dist_eq_prod]
  simp only [mem_singleton, forall_eq]
  by_cases hE : E w <;> by_cases hz : (G.parentsFinset i).restrict w = z <;>
    by_cases hi : w i = x i <;> simp only [hE, hz, hi, and_self, and_true, and_false,
      ite_true, ite_false, zero_mul]
  rw [← prod_mul_prod_compl {i}, prod_singleton, mul_comm]
  congr 1
  rw [kernels_factor, ← hz, ← hi]
  rfl

/-- **Adjustment for direct causes** (Pearl 2009, Theorem 3.2.2, equation (3.13)): the effect of
`do(X_i := x_i)` on any set `Y` is
`P(y | do(x_i)) = ∑_{pa_i} P(y, x_i, pa_i) / P(x_i, pa_i) * P(pa_i)`,
that is `∑_{pa_i} P(y | x_i, pa_i) P(pa_i)`, provided every parent configuration of positive
probability gives `x_i` positive probability. Pearl states it for `Y` disjoint from
`{X_i} ∪ PA_i`; the identity holds for every `Y`. A parent configuration of probability zero
contributes `_ / 0 * 0 = 0` on the right and `0` on the left, so the convention `x / 0 = 0`
carries nothing. -/
theorem effect_singleton_eq_sum (i : V) (x : ∀ v, α v) (Y : Finset V) (y : ∀ v, α v)
    (hpos : ∀ z : (∀ u : G.parentsFinset i, α u),
      0 < M.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) →
      0 < M.dist.probOf (fun w => w i = x i ∧ (G.parentsFinset i).restrict w = z)) :
    M.effect {i} x Y y = ∑ z : (∀ u : G.parentsFinset i, α u),
      M.dist.probOf (fun w => (∀ v ∈ Y, w v = y v) ∧ w i = x i ∧
          (G.parentsFinset i).restrict w = z) /
        M.dist.probOf (fun w => w i = x i ∧ (G.parentsFinset i).restrict w = z) *
        M.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) := by
  rw [effect, FiniteDist.margAt_eq_probOf,
    FiniteDist.probOf_eq_sum_univ _ (P := fun w => ∀ v ∈ Y, w v = y v)
      ((G.parentsFinset i).restrict (π := α))]
  refine sum_congr rfl fun z _ => ?_
  rcases (FiniteDist.probOf_nonneg M.dist
    (P := fun w => (G.parentsFinset i).restrict w = z)).eq_or_lt with h0 | hz
  · -- a parent configuration of probability zero contributes nothing on either side
    have hle : (M.intervene {i} x).dist.probOf
        (fun w => (∀ v ∈ Y, w v = y v) ∧ (G.parentsFinset i).restrict w = z) ≤
          M.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) := by
      rw [← M.probOf_intervene_singleton_parents i x z]
      exact FiniteDist.probOf_mono _ fun w hw => hw.2
    rw [← h0] at hle ⊢
    rw [mul_zero]
    exact le_antisymm hle (FiniteDist.probOf_nonneg _)
  · have hxz := hpos z hz
    have hc : M.dist.probOf (fun w => w i = x i ∧ (G.parentsFinset i).restrict w = z) =
        M.kernel i z (x i) * M.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) :=
      M.probOf_and_parents_eq i z (x i)
    have hk : M.kernel i z (x i) ≠ 0 := by
      intro hk
      rw [hc, hk, zero_mul] at hxz
      exact lt_irrefl 0 hxz
    have key := M.probOf_intervene_singleton_mul i x z (fun w => ∀ v ∈ Y, w v = y v)
    rw [hc, ← key]
    field_simp

/-! ### Identifiability -/

end SCM

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite Markovian structural causal model on `G` bundled with its noise types (in `Type`),
so that models with different noise spaces form one type. Since every finite type is equivalent
to some `Fin n`, the restriction of the noise types to `Type` loses no generality. The value
types `α` are a parameter of the type and are not bundled (see `SCM.IdentifiableFrom`). -/
structure SCM.Model (G : Digraph V) [DecidableRel G.Adj] (α : V → Type*) where
  /-- The noise types. -/
  ε : V → Type
  /-- The noise types are finite. -/
  [fintype : ∀ v, Fintype (ε v)]
  /-- The structural causal model. -/
  scm : SCM G α ε

attribute [instance] SCM.Model.fintype

namespace SCM

variable {G : Digraph V} [DecidableRel G.Adj] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)]

/-- The query `Q` is **identifiable** within the class `C` of models on `G` from the observed
vertices `O`: two models of `C` with the same marginal law of the vertices in `O` give the same
value of `Q` (Pearl 2009, Definitions 3.2.3 and 3.2.4). This is `PointIdentified` with the
observed marginal as the observation.

Limitation: the value types `α v` are fixed for all vertices, the unobserved ones included,
whereas Pearl's Definition 3.2.4 compares any two models with graph `G` whatever the domains of
the latent variables. When `O` is not all of `V`, a positive result stated with
`IdentifiableFrom` therefore compares only models whose latent vertices have the same value
types; it holds for every choice of those types, but it does not compare models with different
latent types. With `O = univ` (no latent vertex) and for the negative results (which exhibit
two models in the class) nothing is lost. -/
def IdentifiableFrom (C : Set (Model G α)) (O : Finset V) {β : Type*} (Q : Model G α → β) :
    Prop :=
  PointIdentified C (fun m => m.scm.dist.marginal O) Q

/-- Two joint laws with the same marginal on `O` give the same probability to every event that
depends only on the coordinates in `O`. -/
theorem _root_.CausalInference.FiniteDist.probOf_eq_of_marginal_eq
    {p q : FiniteDist (∀ v, α v)} {O : Finset V} (h : p.marginal O = q.marginal O)
    (P : (∀ v, α v) → Prop) [DecidablePred P]
    (hP : ∀ w w', (∀ v ∈ O, w v = w' v) → (P w ↔ P w')) : p.probOf P = q.probOf P := by
  obtain ⟨w₀⟩ := p.nonempty
  have key : ∀ r : FiniteDist (∀ v, α v),
      r.probOf P = (r.marginal O).probOf (fun a => P (FiniteDist.override O a w₀)) := by
    intro r
    rw [FiniteDist.marginal, FiniteDist.probOf_map]
    exact r.probOf_congr fun w =>
      hP _ _ fun v hv => (FiniteDist.override_of_mem (O.restrict w) w₀ hv).symm
  rw [key p, key q, h]

/-- Two distributions with the same marginal on all coordinates are equal. -/
theorem _root_.CausalInference.FiniteDist.eq_of_marginal_univ_eq {p q : FiniteDist (∀ v, α v)}
    (h : p.marginal univ = q.marginal univ) : p = q := by
  ext w
  rw [← FiniteDist.margAt_univ p, ← FiniteDist.margAt_univ q, ← FiniteDist.marginal_restrict,
    ← FiniteDist.marginal_restrict, h]

/-- **Two models with the same strictly positive joint law have the same interventional laws**
(the truncated factorization is a function of the observational law). If `M` and `M'` on the same
graph induce the same distribution and it gives every configuration positive mass, then for
every set `X` and value `x` the distributions induced by `do(X := x)` agree: every parent row
has positive probability, so the kernels of the two models agree there (uniqueness of the
kernels on the support, `Digraph.MarkovKernels.kernel_eq_of_probOf_pos`), and the truncated
factorization `SCM.dist_intervene` finishes. -/
theorem dist_intervene_eq_of_dist_eq {ε ε' : V → Type*} [∀ v, Fintype (ε v)]
    [∀ v, Fintype (ε' v)] (M : SCM G α ε)
    (M' : SCM G α ε') (hd : M.dist = M'.dist) (hpos : ∀ w, 0 < M.dist w) (X : Finset V)
    (x : ∀ v, α v) : (M.intervene X x).dist = (M'.intervene X x).dist := by
  ext y
  rw [dist_intervene, dist_intervene]
  split_ifs
  · refine prod_congr rfl fun v _ => ?_
    exact M.kernels.kernel_eq_of_probOf_pos M.acyclic M'.kernels M.dist_eq_prod
      (fun w => by rw [hd]; exact M'.dist_eq_prod w) v _ _
      ((hpos y).trans_le (M.dist.le_probOf y rfl))
  · rfl

/-- **Identification when all variables are observed** (Pearl 2009, Corollary 3.2.6): for every
set `X` and value `x`, the distribution induced by `do(X := x)` is identifiable from the joint
law of all vertices, within the class of models on `G` with strictly positive joint law. -/
theorem identifiableFrom_dist_intervene (X : Finset V) (x : ∀ v, α v) :
    IdentifiableFrom {m : Model G α | ∀ w, 0 < m.scm.dist w} univ
      (fun m => (m.scm.intervene X x).dist) :=
  fun m hm m' _ hobs =>
    dist_intervene_eq_of_dist_eq m.scm m'.scm (FiniteDist.eq_of_marginal_univ_eq hobs) hm X x

/-- **Identification when all variables are observed** (Pearl 2009, Corollary 3.2.6), for the
causal effect `P(Y = y | do(X := x))` of any set `X` on any set `Y`. -/
theorem identifiableFrom_effect (X : Finset V) (x : ∀ v, α v) (Y : Finset V) (y : ∀ v, α v) :
    IdentifiableFrom {m : Model G α | ∀ w, 0 < m.scm.dist w} univ
      (fun m => m.scm.effect X x Y y) := by
  intro m hm m' hm' hobs
  have h := identifiableFrom_dist_intervene X x m hm m' hm' hobs
  simp only at h ⊢
  rw [effect, effect, h]

/-- The effect of an intervention on a single vertex is identifiable from the joint law of all
vertices, within the class of models with strictly positive distribution: the case `X = {i}` of
`SCM.identifiableFrom_effect`. `SCM.identifiableFrom_effect_singleton_of_subset` needs only
`{i} ∪ PA_i ∪ Y` observed and overlap on the supported parent rows. -/
theorem identifiableFrom_effect_singleton (i : V) (x : ∀ v, α v) (Y : Finset V)
    (y : ∀ v, α v) :
    IdentifiableFrom {m : Model G α | ∀ w, 0 < m.scm.dist w} univ
      (fun m => m.scm.effect {i} x Y y) :=
  identifiableFrom_effect {i} x Y y

/-- **Identification by adjustment for the direct causes** (Pearl 2009, Theorem 3.2.5, for a
single intervened vertex): the effect of `do(X_i := x_i)` on any set `Y` is identifiable from
the marginal law of any observed set `O ⊇ {i} ∪ PA_i ∪ Y`, within the class of models on `G`
in which every parent configuration of positive probability gives `x_i` positive probability
(overlap on the supported parent rows). All other vertices may be latent. The identifying
formula is the adjustment for direct causes, `SCM.effect_singleton_eq_sum`.

Pearl's class is the models with strictly positive observed law; the overlap condition is
weaker. Pearl states the theorem for a set `X` and its parents `PA_X`; this is the case of one
vertex. The value types of the latent vertices are fixed by the model type (see
`SCM.IdentifiableFrom`). -/
theorem identifiableFrom_effect_singleton_of_subset (i : V) (x : ∀ v, α v) (Y : Finset V)
    (y : ∀ v, α v) {O : Finset V} (hO : insert i (G.parentsFinset i) ∪ Y ⊆ O) :
    IdentifiableFrom {m : Model G α | ∀ z : (∀ u : G.parentsFinset i, α u),
        0 < m.scm.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) →
        0 < m.scm.dist.probOf (fun w => w i = x i ∧ (G.parentsFinset i).restrict w = z)}
      O (fun m => m.scm.effect {i} x Y y) := by
  intro m hm m' hm' hobs
  simp only at hobs ⊢
  rw [m.scm.effect_singleton_eq_sum i x Y y hm, m'.scm.effect_singleton_eq_sum i x Y y hm']
  have hw : ∀ w w' : ∀ v, α v, (∀ v ∈ O, w v = w' v) →
      (G.parentsFinset i).restrict w = (G.parentsFinset i).restrict w' ∧ w i = w' i ∧
        ∀ v ∈ Y, w v = w' v := fun w w' h =>
    ⟨funext fun p => h p (hO (mem_union_left _ (mem_insert_of_mem p.2))),
      h i (hO (mem_union_left _ (mem_insert_self _ _))),
      fun v hv => h v (hO (mem_union_right _ hv))⟩
  refine sum_congr rfl fun z _ => ?_
  have e1 := FiniteDist.probOf_eq_of_marginal_eq hobs
    (fun w => (∀ v ∈ Y, w v = y v) ∧ w i = x i ∧ (G.parentsFinset i).restrict w = z)
    fun w w' h => by
      obtain ⟨h1, h2, h3⟩ := hw w w' h
      rw [h1, h2]
      exact and_congr_left' (forall₂_congr fun v hv => by rw [h3 v hv])
  have e2 := FiniteDist.probOf_eq_of_marginal_eq hobs
    (fun w => w i = x i ∧ (G.parentsFinset i).restrict w = z)
    fun w w' h => by
      obtain ⟨h1, h2, -⟩ := hw w w' h
      rw [h1, h2]
  have e3 := FiniteDist.probOf_eq_of_marginal_eq hobs
    (fun w => (G.parentsFinset i).restrict w = z)
    fun w w' h => by
      obtain ⟨h1, -, -⟩ := hw w w' h
      rw [h1]
  rw [e1, e2, e3]

end SCM

/-! ### The bow pattern: a non-identifiable effect -/

namespace SCM.BowExample

/-- The bow graph on `Fin 3`: vertex `0` is a latent common cause `U` of `1 = X` and `2 = Y`, and
there is the edge `X → Y` (Pearl 2009, Figure 3.7(a), with the confounding arc made explicit). -/
def bow : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j ≠ 0) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel bow.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem bow_isAcyclic : bow.IsAcyclic := by decide

theorem zero_mem_parentsFinset {v : Fin 3} (h : v ≠ 0) : (0 : Fin 3) ∈ bow.parentsFinset v :=
  Digraph.mem_parentsFinset.2 (Or.inl ⟨rfl, h⟩)

theorem one_mem_parentsFinset {v : Fin 3} (h0 : v ≠ 0) (h1 : v ≠ 1) :
    (1 : Fin 3) ∈ bow.parentsFinset v := by
  fin_cases v
  · exact absurd rfl h0
  · exact absurd rfl h1
  · decide

/-- A biased coin with `P(true) = 1/4`. -/
noncomputable def quarterCoin : FiniteDist Bool where
  mass b := if b then 1 / 4 else 3 / 4
  nonneg b := by cases b <;> norm_num
  sum_eq_one := by norm_num [Fintype.sum_bool]

/-- The noise laws: fair bits for `U` and `X`, and the biased coin for `Y`. -/
noncomputable def bowNoise (v : Fin 3) : FiniteDist Bool :=
  if v = 2 then quarterCoin else FiniteDist.uniform

theorem bowNoise_pos (v : Fin 3) (b : Bool) : 0 < bowNoise v b := by
  unfold bowNoise
  split_ifs
  · cases b <;> norm_num [quarterCoin]
  · simp

/-- Model A: `U := ε_U`, `X := U`, `Y := U xor ε_Y`. The treatment has no effect on `Y`. -/
noncomputable def modelA : SCM bow (fun _ => Bool) (fun _ => Bool) where
  acyclic := bow_isAcyclic
  f v z e := if h0 : v = 0 then e else if v = 1 then z ⟨0, zero_mem_parentsFinset h0⟩ else
    xor (z ⟨0, zero_mem_parentsFinset h0⟩) e
  noise := bowNoise

/-- Model B: `U := ε_U`, `X := U`, `Y := X xor ε_Y`. The outcome responds to the treatment. -/
noncomputable def modelB : SCM bow (fun _ => Bool) (fun _ => Bool) where
  acyclic := bow_isAcyclic
  f v z e := if h0 : v = 0 then e else if h1 : v = 1 then z ⟨0, zero_mem_parentsFinset h0⟩ else
    xor (z ⟨1, one_mem_parentsFinset h0 h1⟩) e
  noise := bowNoise

theorem modelA_solve (u : Fin 3 → Bool) : modelA.solve u = ![u 0, u 0, xor (u 0) (u 2)] := by
  refine (modelA.isSolution_iff.1 fun v => ?_).symm
  fin_cases v <;> simp [modelA, Finset.restrict]

theorem modelB_solve (u : Fin 3 → Bool) : modelB.solve u = ![u 0, u 0, xor (u 0) (u 2)] := by
  refine (modelB.isSolution_iff.1 fun v => ?_).symm
  fin_cases v <;> simp [modelB, Finset.restrict]

/-- The two models induce the same joint law (they have the same solution map). -/
theorem modelA_dist_eq_modelB_dist : modelA.dist = modelB.dist := by
  change (FiniteDist.pi bowNoise).map modelA.solve = (FiniteDist.pi bowNoise).map modelB.solve
  congr 1
  funext u
  rw [modelA_solve, modelB_solve]

/-- The treatment value `X = true`, as a configuration. -/
def treat : Fin 3 → Bool := fun _ => true

theorem modelA_solve_intervene (u : Fin 3 → Bool) :
    (modelA.intervene {1} treat).solve u = ![u 0, true, xor (u 0) (u 2)] := by
  refine ((modelA.intervene {1} treat).eq_solve_of_isSolution ?_).symm
  refine modelA.isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton] at hv
    subst hv
    rfl
  · fin_cases v <;> simp_all [modelA, Finset.restrict]

theorem modelB_solve_intervene (u : Fin 3 → Bool) :
    (modelB.intervene {1} treat).solve u = ![u 0, true, xor true (u 2)] := by
  refine ((modelB.intervene {1} treat).eq_solve_of_isSolution ?_).symm
  refine modelB.isSolution_intervene_iff.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_singleton] at hv
    subst hv
    rfl
  · fin_cases v <;> simp_all [modelB, Finset.restrict]

/-- In model A, `P(Y = true | do(X = true)) = 1/2`. -/
theorem modelA_effect : modelA.effect {1} treat {2} treat = 1 / 2 := by
  rw [effect, margAt_dist, noiseDist_intervene]
  simp only [mem_singleton, forall_eq, modelA_solve_intervene]
  change (FiniteDist.pi bowNoise).probOf (fun u => xor (u 0) (u 2) = true) = _
  rw [← FiniteDist.probOf_map (FiniteDist.pi bowNoise) (fun u => (u 0, u 2))
    (fun q => xor q.1 q.2 = true), FiniteDist.map_pi_eval_pair bowNoise (by decide)]
  simp [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type, bowNoise,
    quarterCoin]
  norm_num

/-- In model B, `P(Y = true | do(X = true)) = 3/4`. -/
theorem modelB_effect : modelB.effect {1} treat {2} treat = 3 / 4 := by
  rw [effect, margAt_dist, noiseDist_intervene]
  simp only [mem_singleton, forall_eq, modelB_solve_intervene]
  change (FiniteDist.pi bowNoise).probOf (fun u => xor true (u 2) = true) = _
  rw [FiniteDist.probOf_pi_eval bowNoise 2 (fun e => xor true e = true)]
  simp [FiniteDist.probOf, FiniteDist.prob, sum_filter, bowNoise, quarterCoin]

/-- The observed law of `(X, Y)` is strictly positive in model A. -/
theorem modelA_margAt_pos (w : Fin 3 → Bool) : 0 < modelA.dist.margAt {1, 2} w := by
  rw [margAt_dist]
  have hu : ∀ v ∈ ({1, 2} : Finset (Fin 3)), modelA.solve ![w 1, w 1, xor (w 1) (w 2)] v = w v := by
    intro v hv
    rw [modelA_solve]
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp
  have hm : 0 < modelA.noiseDist ![w 1, w 1, xor (w 1) (w 2)] := by
    change 0 < ∏ v, bowNoise v (![w 1, w 1, xor (w 1) (w 2)] v)
    exact prod_pos fun v _ => bowNoise_pos v _
  exact hm.trans_le (by
    convert modelA.noiseDist.le_probOf
      (P := fun u => ∀ v ∈ ({1, 2} : Finset (Fin 3)), modelA.solve u v = w v) _ hu)

/-- Model A bundled with its noise types. -/
noncomputable def mA : Model bow (fun _ => Bool) := ⟨fun _ => Bool, modelA⟩

/-- Model B bundled with its noise types. -/
noncomputable def mB : Model bow (fun _ => Bool) := ⟨fun _ => Bool, modelB⟩

/-- **The bow pattern is not identifiable** (Pearl 2009, Figure 3.7(a)): with `U` latent and
only `X` and `Y` observed, the effect `P(Y = true | do(X = true))` is not identifiable within the
class of models on the bow graph with strictly positive observed law of `(X, Y)`. Models A and
B have the same observed law and the effects `1/2` and `3/4`. -/
theorem not_identifiableFrom_effect :
    ¬ IdentifiableFrom {m : Model bow (fun _ => Bool) | ∀ w, 0 < m.scm.dist.margAt {1, 2} w}
      {1, 2} (fun m => m.scm.effect {1} treat {2} treat) := by
  intro h
  have hA : ∀ w, 0 < mA.scm.dist.margAt {1, 2} w := modelA_margAt_pos
  have hB : ∀ w, 0 < mB.scm.dist.margAt {1, 2} w := by
    intro w
    change 0 < modelB.dist.margAt {1, 2} w
    rw [← modelA_dist_eq_modelB_dist]
    exact modelA_margAt_pos w
  have := h mA hA mB hB (by
    change modelA.dist.marginal {1, 2} = modelB.dist.marginal {1, 2}
    rw [modelA_dist_eq_modelB_dist])
  change modelA.effect {1} treat {2} treat = modelB.effect {1} treat {2} treat at this
  rw [modelA_effect, modelB_effect] at this
  norm_num at this

/-- **Without positivity the effect is not identifiable even with every vertex observed.** Models
A and B have the same joint law of all three vertices (`modelA_dist_eq_modelB_dist`), which is
not strictly positive (`X = U` almost surely), and the effects `1/2` and `3/4`. Compare
`SCM.identifiableFrom_effect`, which assumes a strictly positive joint law. -/
theorem not_identifiableFrom_effect_of_all_observed :
    ¬ IdentifiableFrom (Set.univ : Set (Model bow (fun _ => Bool))) univ
      (fun m => m.scm.effect {1} treat {2} treat) := by
  intro h
  have := h mA trivial mB trivial (by
    change modelA.dist.marginal univ = modelB.dist.marginal univ
    rw [modelA_dist_eq_modelB_dist])
  change modelA.effect {1} treat {2} treat = modelB.effect {1} treat {2} treat at this
  rw [modelA_effect, modelB_effect] at this
  norm_num at this

/-! #### A witness with full support and every arrow active

In models A and B the treatment equals the latent variable, model A ignores the arrow `X → Y`,
and model B ignores `U → Y`. The second witness below has a strictly positive joint law of all
three vertices and depends on every arrow of the bow graph, so the non-identifiability comes
from the latent variable alone: observing `U` as well would identify the effect
(`SCM.identifiableFrom_effect`). -/

/-- The mass of a biased coin with `P(true) = r` at `b`. -/
noncomputable def bern (r : ℝ) (b : Bool) : ℝ := if b then r else 1 - r

theorem bern_pos {r : ℝ} (h0 : 0 < r) (h1 : r < 1) (b : Bool) : 0 < bern r b := by
  cases b <;> simp [bern] <;> linarith

/-- Markov kernels on the bow graph: `U` is a fair coin, `P(X = true | U) = 1/4` or `3/4` as `U`
is false or true, and `P(Y = true | X = a, U = b) = pY a b`. -/
noncomputable def fullKernels (pY : Bool → Bool → ℝ) (hpY : ∀ a b, 0 < pY a b ∧ pY a b < 1) :
    bow.MarkovKernels (fun _ => Bool) where
  kernel v z b := if h0 : v = 0 then bern (1 / 2) b else if h1 : v = 1 then
      bern (if z ⟨0, zero_mem_parentsFinset h0⟩ then 3 / 4 else 1 / 4) b else
    bern (pY (z ⟨1, one_mem_parentsFinset h0 h1⟩) (z ⟨0, zero_mem_parentsFinset h0⟩)) b
  nonneg v z b := by
    split_ifs
    · exact (bern_pos (by norm_num) (by norm_num) b).le
    · exact (bern_pos (by norm_num) (by norm_num) b).le
    · exact (bern_pos (by norm_num) (by norm_num) b).le
    · exact (bern_pos (hpY _ _).1 (hpY _ _).2 b).le
  sum_eq_one v z := by
    split_ifs <;> simp [bern]

/-- The outcome probabilities of model C: `P(Y = true | X, U)` is `1/4, 1/2` across `U` when
`X = false`, and `1/4, 3/4` when `X = true`. -/
noncomputable def pYC (a b : Bool) : ℝ :=
  if a then (if b then 3 / 4 else 1 / 4) else (if b then 1 / 2 else 1 / 4)

/-- The outcome probabilities of model D: as in model C when `X = false`, and `5/8` for both
values of `U` when `X = true`. -/
noncomputable def pYD (a b : Bool) : ℝ :=
  if a then 5 / 8 else (if b then 1 / 2 else 1 / 4)

theorem pYC_bounds (a b : Bool) : 0 < pYC a b ∧ pYC a b < 1 := by
  cases a <;> cases b <;> norm_num [pYC]

theorem pYD_bounds (a b : Bool) : 0 < pYD a b ∧ pYD a b < 1 := by
  cases a <;> cases b <;> norm_num [pYD]

/-- Model C, with response-function noise realizing `fullKernels pYC`. -/
noncomputable def modelC := (fullKernels pYC pYC_bounds).toSCM bow_isAcyclic

/-- Model D, with response-function noise realizing `fullKernels pYD`. -/
noncomputable def modelD := (fullKernels pYD pYD_bounds).toSCM bow_isAcyclic

theorem fullKernels_factor (pY : Bool → Bool → ℝ) (hpY : ∀ a b, 0 < pY a b ∧ pY a b < 1)
    (w : Fin 3 → Bool) :
    (fullKernels pY hpY).factor 0 w = bern (1 / 2) (w 0) ∧
      (fullKernels pY hpY).factor 1 w = bern (if w 0 then 3 / 4 else 1 / 4) (w 1) ∧
      (fullKernels pY hpY).factor 2 w = bern (pY (w 1) (w 0)) (w 2) :=
  ⟨rfl, rfl, rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem _root_.CausalInference.SCM.kernels_factor_eq {W : Type*} [Fintype W] {H : Digraph W}
    [DecidableRel H.Adj] {β ε : W → Type*} [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    [∀ v, Fintype (ε v)] (N : SCM H β ε) (v : W) (w : ∀ v, β v) :
    N.kernels.factor v w = N.kernel v ((H.parentsFinset v).restrict w) (w v) := rfl

/-- The joint law of the model realizing `fullKernels pY`, as a product of the kernels. -/
theorem dist_fullKernels (pY : Bool → Bool → ℝ) (hpY : ∀ a b, 0 < pY a b ∧ pY a b < 1)
    (w : Fin 3 → Bool) :
    ((fullKernels pY hpY).toSCM bow_isAcyclic).dist w =
      bern (1 / 2) (w 0) * bern (if w 0 then 3 / 4 else 1 / 4) (w 1) *
        bern (pY (w 1) (w 0)) (w 2) := by
  obtain ⟨h0, h1, h2⟩ := fullKernels_factor pY hpY w
  rw [Digraph.MarkovKernels.dist_toSCM, Digraph.MarkovKernels.jointDist_apply,
    Fin.prod_univ_three, h0, h1, h2]

/-- The joint law of all three vertices is strictly positive. -/
theorem dist_fullKernels_pos (pY : Bool → Bool → ℝ) (hpY : ∀ a b, 0 < pY a b ∧ pY a b < 1)
    (w : Fin 3 → Bool) : 0 < ((fullKernels pY hpY).toSCM bow_isAcyclic).dist w := by
  rw [dist_fullKernels]
  refine mul_pos (mul_pos (bern_pos (by norm_num) (by norm_num) _)
    (bern_pos (by split_ifs <;> norm_num) (by split_ifs <;> norm_num) _))
    (bern_pos (hpY _ _).1 (hpY _ _).2 _)

/-- On `Fin 3 → Bool`, the marginal mass on `{1, 2}` is the sum over the value of vertex `0`. -/
theorem margAt_one_two (p : FiniteDist (Fin 3 → Bool)) (w : Fin 3 → Bool) :
    p.margAt {1, 2} w = ∑ b : Bool, p (Function.update w 0 b) := by
  rw [p.margAt_eq_sum_margAt (subset_univ _),
    show (univ \ ({1, 2} : Finset (Fin 3)))ᶜ = ({0} : Finset (Fin 3))ᶜ by decide,
    FiniteDist.sum_agreeOn_compl_singleton]
  simp only [FiniteDist.margAt_univ]

/-- On `Fin 3 → Bool`, the marginal mass on `{2}` is the sum over the values of vertices `1`
and `0`. -/
theorem margAt_two (p : FiniteDist (Fin 3 → Bool)) (w : Fin 3 → Bool) :
    p.margAt {2} w = ∑ a : Bool, ∑ b : Bool, p (Function.update (Function.update w 1 a) 0 b) := by
  rw [p.margAt_eq_sum_margAt (show ({2} : Finset (Fin 3)) ⊆ {1, 2} by decide),
    show (({1, 2} : Finset (Fin 3)) \ {2})ᶜ = ({1} : Finset (Fin 3))ᶜ by decide,
    FiniteDist.sum_agreeOn_compl_singleton]
  simp only [margAt_one_two]

/-- Models C and D induce the same law of the observed pair `(X, Y)`. -/
theorem modelC_marginal_eq_modelD :
    modelC.dist.marginal {1, 2} = modelD.dist.marginal {1, 2} := by
  ext a
  obtain ⟨w₀⟩ := modelC.dist.nonempty
  rw [← FiniteDist.restrict_override {1, 2} a w₀, FiniteDist.marginal_restrict,
    FiniteDist.marginal_restrict]
  generalize FiniteDist.override {1, 2} a w₀ = w
  rw [margAt_one_two, margAt_one_two, modelC, modelD]
  simp only [dist_fullKernels, Fintype.sum_bool, Function.update_self,
    Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide)]
  cases w 1 <;> cases w 2 <;> norm_num [bern, pYC, pYD]

/-- The interventional law of `do(X := true)` in the model realizing `fullKernels pY`. -/
theorem effect_fullKernels (pY : Bool → Bool → ℝ) (hpY : ∀ a b, 0 < pY a b ∧ pY a b < 1) :
    ((fullKernels pY hpY).toSCM bow_isAcyclic).effect {1} treat {2} treat =
      (pY true false + pY true true) / 2 := by
  rw [effect, margAt_two]
  simp only [dist_intervene, Fintype.sum_bool, mem_singleton, forall_eq, Function.update_self,
    Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide), treat]
  rw [show ({1} : Finset (Fin 3))ᶜ = {0, 2} by decide]
  have hf : ∀ v w, ((fullKernels pY hpY).toSCM bow_isAcyclic).kernels.factor v w =
      (fullKernels pY hpY).factor v w := fun v w => by
    rw [SCM.kernels_factor_eq, Digraph.MarkovKernels.kernel_toSCM]
    rfl
  simp only [prod_pair (show (0 : Fin 3) ≠ 2 by decide), hf, ite_true, Bool.false_eq_true,
    ite_false, add_zero]
  rw [(fullKernels_factor pY hpY _).1, (fullKernels_factor pY hpY _).2.2,
    (fullKernels_factor pY hpY _).1, (fullKernels_factor pY hpY _).2.2]
  simp only [Function.update_self, Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide),
    Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide),
    Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide), treat, bern, ite_true,
    Bool.false_eq_true, ite_false]
  ring

/-- In model C, `P(Y = true | do(X = true)) = 1/2`. -/
theorem modelC_effect : modelC.effect {1} treat {2} treat = 1 / 2 := by
  rw [modelC, effect_fullKernels]
  norm_num [pYC]

/-- In model D, `P(Y = true | do(X = true)) = 5/8`. -/
theorem modelD_effect : modelD.effect {1} treat {2} treat = 5 / 8 := by
  rw [modelD, effect_fullKernels]
  norm_num [pYD]

/-- **Every arrow of the bow graph is active in models C and D**: the kernel of `X` depends on
`U`, and the kernel of `Y` depends on `X` (at `U = true`) and on `U` (at `X = false`). The
factors are read at configurations that differ in one parent of the vertex. -/
theorem arrows_active (pY : Bool → Bool → ℝ) (hpY : ∀ a b, 0 < pY a b ∧ pY a b < 1)
    (hX : pY false true ≠ pY true true) (hU : pY false false ≠ pY false true) :
    (fullKernels pY hpY).factor 1 ![false, true, true] ≠
        (fullKernels pY hpY).factor 1 ![true, true, true] ∧
      (fullKernels pY hpY).factor 2 ![true, false, true] ≠
        (fullKernels pY hpY).factor 2 ![true, true, true] ∧
      (fullKernels pY hpY).factor 2 ![false, false, true] ≠
        (fullKernels pY hpY).factor 2 ![true, false, true] := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [(fullKernels_factor pY hpY _).2.1,
    (fullKernels_factor pY hpY _).2.2, bern] <;> norm_num [hX, hU]

/-- Models C and D satisfy the hypotheses of `arrows_active`. -/
theorem pYC_pYD_active :
    (pYC false true ≠ pYC true true ∧ pYC false false ≠ pYC false true) ∧
      (pYD false true ≠ pYD true true ∧ pYD false false ≠ pYD false true) := by
  norm_num [pYC, pYD]

/-- Model C bundled with its noise types. -/
noncomputable def mC : Model bow (fun _ => Bool) := ⟨_, modelC⟩

/-- Model D bundled with its noise types. -/
noncomputable def mD : Model bow (fun _ => Bool) := ⟨_, modelD⟩

/-- **The bow pattern is not identifiable, even with full support and every arrow active**: the
effect `P(Y = true | do(X = true))` is not identifiable from the law of `(X, Y)` within the class
of models on the bow graph whose joint law of all three vertices is strictly positive. Models C
and D are in the class, have the same observed law, every arrow active (`arrows_active` with
`pYC_pYD_active`), and
the effects `1/2` and `5/8`. -/
theorem not_identifiableFrom_effect_of_pos :
    ¬ IdentifiableFrom {m : Model bow (fun _ => Bool) | ∀ w, 0 < m.scm.dist w}
      {1, 2} (fun m => m.scm.effect {1} treat {2} treat) := by
  intro h
  have := h mC (dist_fullKernels_pos pYC pYC_bounds) mD (dist_fullKernels_pos pYD pYD_bounds)
    modelC_marginal_eq_modelD
  change modelC.effect {1} treat {2} treat = modelD.effect {1} treat {2} treat at this
  rw [modelC_effect, modelD_effect] at this
  norm_num at this

end SCM.BowExample

end CausalInference
