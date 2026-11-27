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

* `SCM.probOf_and_parents_eq`: the kernel is the conditional law given the parents,
  `P(x_i = a, pa_i = z) = kernel i z a * P(pa_i = z)`.
* `SCM.effect_singleton_eq_sum` (**adjustment for direct causes**, Pearl 2009, Theorem 3.2.2):
  `P(y | do(x_i)) = ∑_{pa_i} P(y | x_i, pa_i) P(pa_i)`, under the positivity hypothesis that
  every parent configuration of positive probability gives `x_i` positive probability.
* `SCM.identifiableFrom_effect_singleton`: with every vertex observed, the effect of an
  intervention on one vertex is identifiable within the class of models with strictly positive
  distribution (a special case of Pearl 2009, Theorem 3.2.5 and Corollary 3.2.6).
* `SCM.BowExample.not_identifiableFrom_effect` (Pearl 2009, Figure 3.7(a), the bow pattern):
  with a latent common cause `U` of `X` and `Y` and the edge `X → Y`, two models have the same
  strictly positive observed law of `(X, Y)` and different effects `P(Y = 1 | do(X = 1))`
  (`1/2` and `3/4`), so the effect is not identifiable.

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
to some `Fin n`, the restriction of the noise types to `Type` loses no generality. -/
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
observed marginal as the observation. -/
def IdentifiableFrom (C : Set (Model G α)) (O : Finset V) {β : Type*} (Q : Model G α → β) :
    Prop :=
  PointIdentified C (fun m => m.scm.dist.marginal O) Q

/-- Two distributions with the same marginal on all coordinates are equal. -/
theorem _root_.CausalInference.FiniteDist.eq_of_marginal_univ_eq {p q : FiniteDist (∀ v, α v)}
    (h : p.marginal univ = q.marginal univ) : p = q := by
  ext w
  rw [← FiniteDist.margAt_univ p, ← FiniteDist.margAt_univ q, ← FiniteDist.marginal_restrict,
    ← FiniteDist.marginal_restrict, h]

/-- **Identification when all variables are observed** (a special case of Pearl 2009,
Theorem 3.2.5 and Corollary 3.2.6): the effect of an intervention on a single vertex is
identifiable from the joint law of all vertices, within the class of models with strictly
positive distribution, by the adjustment formula for direct causes. -/
theorem identifiableFrom_effect_singleton (i : V) (x : ∀ v, α v) (Y : Finset V)
    (y : ∀ v, α v) :
    IdentifiableFrom {m : Model G α | ∀ w, 0 < m.scm.dist w} univ
      (fun m => m.scm.effect {i} x Y y) := by
  intro m hm m' hm' hobs
  have hd : m.scm.dist = m'.scm.dist := FiniteDist.eq_of_marginal_univ_eq hobs
  have hpos : ∀ (n : Model G α), (∀ w, 0 < n.scm.dist w) → ∀ z : (∀ u : G.parentsFinset i, α u),
      0 < n.scm.dist.probOf (fun w => (G.parentsFinset i).restrict w = z) →
      0 < n.scm.dist.probOf (fun w => w i = x i ∧ (G.parentsFinset i).restrict w = z) := by
    intro n hn z _
    obtain ⟨w, hz, hi⟩ := n.scm.exists_restrict_parents_eq i z (x i)
    exact (hn w).trans_le (n.scm.dist.le_probOf w ⟨hi, hz⟩)
  simp only
  rw [m.scm.effect_singleton_eq_sum i x Y y (hpos m hm),
    m'.scm.effect_singleton_eq_sum i x Y y (hpos m' hm'), hd]

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

end SCM.BowExample

end CausalInference
