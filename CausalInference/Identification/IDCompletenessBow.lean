/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDCanonical

/-!
# Completeness of the identification algorithm for graphs with a bow

Let `G` be an acyclic directed mixed graph on `V` with an edge `x → y` and a bidirected edge
`x ↔ y` (a bow). Take the canonical DAG of `G` (`ADMG.canonicalDAG`), with every vertex of `G`
observed. Then:

* the identification algorithm fails for the effect of `x` on `y`, on `G` and on the latent
  projection of the canonical DAG (`IDCompletenessBow.idAlg_eq_none`,
  `IDCompletenessBow.idAlg_canonical_eq_none`);
* for every configuration `w`, the effect `P(y = w_y | do(x := w_x))` is not identifiable from
  the observed law within the class of models on the canonical DAG whose observed law is
  strictly positive (`IDCompletenessBow.not_identifiableFrom`).

So for these graphs and this query, the algorithm decides identifiability
(`IDCompletenessBow.identifiableFrom_iff`): the converse of the soundness theorem
`SCM.identifiableFrom_of_idAlg` holds.

The two models have Boolean values. All latent vertices are fair bits, and every vertex other
than `x` and `y` is a fair bit independent of its parents. With `u` the latent vertex of
`x ↔ y`, both models set `x = u`; in model one `y` is `u` flipped with probability `1/4`, in
model two `y` is `x` flipped with probability `1/4`. The joint laws of the two models are equal
(on the support `x = u`, the two kernels of `y` agree), and strictly positive on the observed
vertices. Under `do(x := a)`, the probability of `y = b` is `1/2` in model one and `3/4` or `1/4`
in model two.

The bow itself is the instance `IDCompletenessBow.bow2_identifiableFrom_iff`.

## Main definitions

* `IDCompletenessBow.bernR`, `IDCompletenessBow.boolKernels`: Boolean kernels from success
  probabilities in `[0, 1]` that read the parent values.
-/

@[expose] public section

namespace CausalInference

namespace IDCompletenessBow

open Finset

/-! ### Boolean kernels from success probabilities -/

section Kernels

variable {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj]

/-- The mass of the Boolean value `b` under the Bernoulli law with success probability `p`. -/
def bernR (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- The two Bernoulli masses sum to one. -/
theorem bernR_add_not (p : ℝ) (b : Bool) : bernR p b + bernR p (!b) = 1 := by
  cases b <;> simp [bernR]

/-- A parent configuration of `v`, extended by `false` outside the parents. -/
def extendPar (v : V) (z : D.parentsFinset v → Bool) : V → Bool :=
  fun u => if h : u ∈ D.parentsFinset v then z ⟨u, h⟩ else false

/-- The extended parent configuration reads the parent values. -/
theorem extendPar_restrict_of_adj {u v : V} (h : D.Adj u v) (σ : V → Bool) :
    extendPar D v ((D.parentsFinset v).restrict σ) u = σ u := by
  simp [extendPar, h]

/-- The Markov kernels whose law at `v` is the Bernoulli law with success probability
`θ v z`, read at the parent configuration `z` extended by `false`. -/
noncomputable def boolKernels (θ : V → (V → Bool) → ℝ) (hθ : ∀ v z, 0 ≤ θ v z ∧ θ v z ≤ 1) :
    D.MarkovKernels (fun _ => Bool) where
  kernel v z b := bernR (θ v (extendPar D v z)) b
  nonneg v z b := by
    cases b <;> simp [bernR, (hθ v _).1, (hθ v _).2]
  sum_eq_one v z := by
    simp [bernR]

/-- The factor of `v` in the model of `IDCompletenessBow.boolKernels`. -/
theorem factor_toSCM (θ : V → (V → Bool) → ℝ) (hθ : ∀ v z, 0 ≤ θ v z ∧ θ v z ≤ 1)
    (hD : D.IsAcyclic) (v : V) (σ : V → Bool) :
    ((boolKernels D θ hθ).toSCM hD).kernels.factor v σ =
      bernR (θ v (extendPar D v ((D.parentsFinset v).restrict σ))) (σ v) := by
  change ((boolKernels D θ hθ).toSCM hD).kernel v _ (σ v) = _
  rw [Digraph.MarkovKernels.kernel_toSCM]
  rfl

end Kernels

/-- A finite distribution, a set `A` and an involution `φ` exchanging `A` and its complement:
if `q' P(σ) = q P(φ σ)` on `A` with `q + q' = 1`, then `P(A) = q`. -/
theorem prob_eq_of_involution {Ω : Type*} [Fintype Ω] (P : FiniteDist Ω)
    (A : Finset Ω) (φ : Ω → Ω) (hφ : ∀ σ, φ (φ σ) = σ) (hA : ∀ σ, φ σ ∈ A ↔ σ ∉ A)
    {q q' : ℝ} (hq : q + q' = 1) (h : ∀ σ ∈ A, q' * P σ = q * P (φ σ)) : P.prob A = q := by
  classical
  have e : ∑ σ ∈ Aᶜ, P σ = ∑ σ ∈ A, P (φ σ) :=
    sum_nbij' φ φ (fun σ hσ => (hA σ).2 (mem_compl.1 hσ))
      (fun σ hσ => mem_compl.2 fun h => (hA σ).1 h hσ)
      (fun σ _ => hφ σ) (fun σ _ => hφ σ) (fun σ _ => by rw [hφ])
  have htot : P.prob A + ∑ σ ∈ Aᶜ, P σ = 1 := by
    rw [FiniteDist.prob, sum_add_sum_compl, P.sum_eq_one]
  have hs : q' * P.prob A = q * ∑ σ ∈ A, P (φ σ) := by
    rw [FiniteDist.prob, mul_sum, mul_sum]
    exact sum_congr rfl h
  rw [e] at htot
  linear_combination hs + q * htot - P.prob A * hq

/-! ### The two models on the canonical DAG -/

variable {V : Type} [Fintype V] [DecidableEq V] (G : ADMG V) [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj] (x y : V)

/-- The success probability of `y`: `3/4` when the read bit is true, `1/4` otherwise. -/
noncomputable def tY (c : Bool) : ℝ := if c then 3 / 4 else 1 / 4

/-- Flipping both the read bit and the value leaves the mass of `y` unchanged. -/
theorem bernR_tY_not (c b : Bool) : bernR (tY (!c)) (!b) = bernR (tY c) b := by
  cases c <;> cases b <;> norm_num [bernR, tY]

/-- The latent vertex of `x ↔ y` in the canonical DAG. -/
abbrev lat : V ⊕ V × V := .inr (x, y)

/-- The success probabilities of model one (`i = false`) and model two (`i = true`): `x` copies
the latent `u` of `x ↔ y`; `y` reads `u` (model one) or `x` (model two); every other vertex is a
fair bit. -/
noncomputable def θ (i : Bool) (v : V ⊕ V × V) (σ : V ⊕ V × V → Bool) : ℝ :=
  if v = .inl x then (if σ (lat x y) then 1 else 0)
  else if v = .inl y then tY (if i then σ (.inl x) else σ (lat x y))
  else 1 / 2

omit [Fintype V] in
/-- The success probabilities lie in `[0, 1]`. -/
theorem θ_mem (i : Bool) (v : V ⊕ V × V) (σ : V ⊕ V × V → Bool) :
    0 ≤ θ x y i v σ ∧ θ x y i v σ ≤ 1 := by
  unfold θ tY
  split_ifs <;> norm_num

variable {G x y}

variable (hG : G.IsAcyclic)

variable (x y) in
/-- The model `i` on the canonical DAG. -/
noncomputable def model (i : Bool) :=
  (boolKernels G.canonicalDAG (θ x y i) (θ_mem x y i)).toSCM hG.canonicalDAG

variable (hxy : G.directed.Adj x y) (hb : G.bidirected.Adj x y)

omit [Fintype V] [DecidableEq V] [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj] in
include hb in
/-- The latent vertex of `x ↔ y` is a parent of `x`. -/
theorem adj_lat_x : G.canonicalDAG.Adj (lat x y) (.inl x) :=
  ADMG.canonicalDAG_adj_inr_inl.2 ⟨hb, .inl rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.directed.Adj]
  [DecidableRel G.bidirected.Adj] in
include hb in
/-- The latent vertex of `x ↔ y` is a parent of `y`. -/
theorem adj_lat_y : G.canonicalDAG.Adj (lat x y) (.inl y) :=
  ADMG.canonicalDAG_adj_inr_inl.2 ⟨hb, .inr rfl⟩

include hb in
/-- The factor of `x`: a point mass at the latent bit `u`. -/
theorem factor_x (i : Bool) (σ : V ⊕ V × V → Bool) :
    (model x y hG i).kernels.factor (.inl x) σ =
      bernR (if σ (lat x y) then 1 else 0) (σ (.inl x)) := by
  rw [model, factor_toSCM]
  simp [θ, extendPar_restrict_of_adj _ (adj_lat_x hb)]

include hb in
/-- The factor of `y` in model one reads `u`. -/
theorem factor_y_false (σ : V ⊕ V × V → Bool) :
    (model x y hG false).kernels.factor (.inl y) σ = bernR (tY (σ (lat x y))) (σ (.inl y)) := by
  have hne : (Sum.inl y : V ⊕ V × V) ≠ .inl x := fun h => hb.ne (Sum.inl_injective h).symm
  rw [model, factor_toSCM]
  simp [θ, hne, extendPar_restrict_of_adj _ (adj_lat_y hb)]

include hb hxy in
/-- The factor of `y` in model two reads `x`. -/
theorem factor_y_true (σ : V ⊕ V × V → Bool) :
    (model x y hG true).kernels.factor (.inl y) σ = bernR (tY (σ (.inl x))) (σ (.inl y)) := by
  have hne : (Sum.inl y : V ⊕ V × V) ≠ .inl x := fun h => hb.ne (Sum.inl_injective h).symm
  rw [model, factor_toSCM]
  simp [θ, hne, extendPar_restrict_of_adj _ (ADMG.canonicalDAG_adj_inl_inl.2 hxy)]

/-- Every other vertex is a fair bit. -/
theorem factor_other (i : Bool) {v : V ⊕ V × V} (hx : v ≠ .inl x) (hy : v ≠ .inl y)
    (σ : V ⊕ V × V → Bool) : (model x y hG i).kernels.factor v σ = 1 / 2 := by
  rw [model, factor_toSCM]
  simp only [θ, hx, hy, ite_false]
  cases σ v <;> norm_num [bernR]

include hb hxy in
/-- **The two models have the same joint law.** -/
theorem dist_model_eq : (model x y hG false).dist = (model x y hG true).dist := by
  ext σ
  rw [SCM.dist_eq_prod, SCM.dist_eq_prod]
  by_cases h : σ (.inl x) = σ (lat x y)
  · refine prod_congr rfl fun v _ => ?_
    by_cases hx : v = .inl x
    · subst hx
      rw [factor_x hG hb, factor_x hG hb]
    by_cases hy : v = .inl y
    · subst hy
      rw [factor_y_false hG hb, factor_y_true hG hxy hb, h]
    · rw [factor_other hG _ hx hy, factor_other hG _ hx hy]
  · have h0 : ∀ i, (model x y hG i).kernels.factor (.inl x) σ = 0 := fun i => by
      rw [factor_x hG hb]
      revert h
      cases σ (.inl x) <;> cases σ (lat x y) <;> simp [bernR]
    rw [prod_eq_zero (f := fun v => (model x y hG false).kernels.factor v σ) (mem_univ _)
        (h0 false),
      prod_eq_zero (f := fun v => (model x y hG true).kernels.factor v σ) (mem_univ _) (h0 true)]

include hb in
/-- **Positivity**: the observed law of model one is strictly positive. -/
theorem margAt_pos (w : V ⊕ V × V → Bool) :
    0 < (model x y hG false).dist.margAt ADMG.canonicalObs w := by
  let σ : V ⊕ V × V → Bool :=
    Sum.elim (fun v => w (.inl v)) fun p => if p = (x, y) then w (.inl x) else false
  have hσ : σ ∈ FiniteDist.agreeOn ADMG.canonicalObs w := by
    rw [FiniteDist.mem_agreeOn]
    intro s hs
    obtain ⟨v, -, rfl⟩ := mem_map.1 hs
    rfl
  have hpos : 0 < (model x y hG false).dist σ := by
    rw [SCM.dist_eq_prod]
    refine prod_pos fun v _ => ?_
    by_cases hx : v = .inl x
    · subst hx
      rw [factor_x hG hb]
      have : σ (lat x y) = σ (.inl x) := by simp [σ]
      rw [this]
      cases σ (.inl x) <;> norm_num [bernR]
    by_cases hy : v = .inl y
    · subst hy
      rw [factor_y_false hG hb]
      cases σ (lat x y) <;> cases σ (.inl y) <;> norm_num [bernR, tY]
    · rw [factor_other hG _ hx hy]
      norm_num
  rw [FiniteDist.margAt, FiniteDist.prob]
  exact hpos.trans_le (single_le_sum (fun τ _ => (model x y hG false).dist.nonneg τ) hσ)

/-- The law of model `i` under `do(x := w_x)`, at a configuration `σ`. -/
theorem dist_intervene_model (i : Bool) (hne : (Sum.inl y : V ⊕ V × V) ≠ .inl x)
    (w σ : V ⊕ V × V → Bool) :
    ((model x y hG i).intervene {.inl x} w).dist σ =
      if σ (.inl x) = w (.inl x) then (model x y hG i).kernels.factor (.inl y) σ *
        (1 / 2) ^ ((({.inl x}ᶜ : Finset (V ⊕ V × V)).erase (.inl y)).card) else 0 := by
  rw [SCM.dist_intervene]
  simp only [mem_singleton, forall_eq]
  split_ifs
  · have hy : (Sum.inl y : V ⊕ V × V) ∈ ({Sum.inl x}ᶜ : Finset (V ⊕ V × V)) :=
      mem_compl.2 fun h => hne (mem_singleton.1 h)
    rw [← mul_prod_erase _ _ hy]
    congr 1
    rw [prod_congr rfl fun v hv => factor_other hG i
      (fun h => (mem_compl.1 (mem_erase.1 hv).2) (mem_singleton.2 h)) (mem_erase.1 hv).1 σ,
      prod_const]
  · rfl

include hb in
/-- Under `do(x := w_x)`, model one gives `y = w_y` probability `1/2`. -/
theorem effect_false (w : V ⊕ V × V → Bool) :
    (model x y hG false).effect {.inl x} w {.inl y} w = 1 / 2 := by
  have hne : (Sum.inl y : V ⊕ V × V) ≠ .inl x := fun h => hb.ne (Sum.inl_injective h).symm
  have hlx : (lat x y : V ⊕ V × V) ≠ .inl x := Sum.inr_ne_inl
  have hly : (lat x y : V ⊕ V × V) ≠ .inl y := Sum.inr_ne_inl
  let φ : (V ⊕ V × V → Bool) → V ⊕ V × V → Bool := fun σ =>
    Function.update (Function.update σ (.inl y) (!σ (.inl y))) (lat x y) (!σ (lat x y))
  have hφx : ∀ σ, φ σ (.inl x) = σ (.inl x) := fun σ => by
    simp [φ, hne.symm, hlx.symm]
  have hφy : ∀ σ, φ σ (.inl y) = !σ (.inl y) := fun σ => by
    simp [φ, hly.symm]
  have hφu : ∀ σ, φ σ (lat x y) = !σ (lat x y) := fun σ => by
    simp [φ]
  rw [SCM.effect, FiniteDist.margAt]
  refine prob_eq_of_involution (q' := 1 / 2) _ _ φ (fun σ => ?_) (fun σ => ?_) (by norm_num)
    fun σ _ => ?_
  · funext s
    by_cases hs : s = lat x y
    · subst hs
      simp [hφu]
    by_cases hs' : s = .inl y
    · subst hs'
      simp [hφy]
    · simp [φ, hs, hs']
  · simp only [FiniteDist.mem_agreeOn, mem_singleton, forall_eq, hφy]
    cases σ (.inl y) <;> cases w (.inl y) <;> simp
  · rw [dist_intervene_model hG _ hne, dist_intervene_model hG _ hne, hφx,
      factor_y_false hG hb, factor_y_false hG hb, hφu, hφy, bernR_tY_not]

include hb hxy in
/-- Under `do(x := w_x)`, model two gives `y = w_y` probability `3/4` or `1/4`. -/
theorem effect_true (w : V ⊕ V × V → Bool) :
    (model x y hG true).effect {.inl x} w {.inl y} w = bernR (tY (w (.inl x))) (w (.inl y)) := by
  have hne : (Sum.inl y : V ⊕ V × V) ≠ .inl x := fun h => hb.ne (Sum.inl_injective h).symm
  let φ : (V ⊕ V × V → Bool) → V ⊕ V × V → Bool := fun σ =>
    Function.update σ (.inl y) (!σ (.inl y))
  have hφx : ∀ σ, φ σ (.inl x) = σ (.inl x) := fun σ => by
    simp [φ, hne.symm]
  have hφy : ∀ σ, φ σ (.inl y) = !σ (.inl y) := fun σ => by simp [φ]
  rw [SCM.effect, FiniteDist.margAt]
  refine prob_eq_of_involution _ _ φ (fun σ => ?_) (fun σ => ?_)
    (bernR_add_not _ (w (.inl y))) fun σ hσ => ?_
  · simp [φ]
  · simp only [FiniteDist.mem_agreeOn, mem_singleton, forall_eq, hφy]
    cases σ (.inl y) <;> cases w (.inl y) <;> simp
  · simp only [FiniteDist.mem_agreeOn, mem_singleton, forall_eq] at hσ
    rw [dist_intervene_model hG _ hne, dist_intervene_model hG _ hne, hφx,
      factor_y_true hG hxy hb, factor_y_true hG hxy hb, hφx, hφy, hσ]
    split_ifs with h
    · rw [h]
      ring
    · ring

include hG hxy hb in
/-- **Non-identifiability for a bow.** On the canonical DAG of an acyclic `G` with `x → y` and
`x ↔ y`, with every vertex of `G` observed, the effect `P(y = w_y | do(x := w_x))` is not
identifiable from the observed law within the class of models whose observed law is strictly
positive, for any configuration `w`. -/
theorem not_identifiableFrom (w : V ⊕ V × V → Bool) :
    ¬ SCM.IdentifiableFrom
      {m : SCM.Model G.canonicalDAG (fun _ => Bool) |
        ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
      (fun m => m.scm.effect {.inl x} w {.inl y} w) := by
  intro h
  have heq := dist_model_eq hG hxy hb
  have := h ⟨_, model x y hG false⟩ (margAt_pos hG hb) ⟨_, model x y hG true⟩
    (fun w => by rw [← heq]; exact margAt_pos hG hb w)
    (by
      change (model x y hG false).dist.marginal _ = (model x y hG true).dist.marginal _
      rw [heq])
  change (model x y hG false).effect _ w _ w = (model x y hG true).effect _ w _ w at this
  rw [effect_false hG hb, effect_true hG hxy hb] at this
  revert this
  cases w (.inl x) <;> cases w (.inl y) <;> norm_num [bernR, tY]

/-! ### Failure of the algorithm -/

include hxy hb in
/-- **The algorithm fails for a bow.** If `G` has `x → y` and `x ↔ y`, the algorithm fails for
the effect of `x` on `y` with every vertex observed: the district `d` of `y` among the
ancestors of `y` outside `x`, enlarged by `x`, is a failure witness. -/
theorem idAlg_eq_none (ord : V → ℕ) : idAlg G ord univ {x} {y} = none := by
  have hne : y ≠ x := hb.ne.symm
  have h₁ : {x} ⊆ (univ : Finset V) ∧ {y} ⊆ univ \ {x} :=
    ⟨subset_univ _, by simpa using hne⟩
  rw [idAlg_eq_none_iff ord h₁]
  set D := ancIn G (univ \ {x}) {y}
  set d := (G.restrict ↑D).districtFinset y
  have hyD : y ∈ D := subset_ancIn (by simpa using hne) (mem_singleton_self y)
  have hd : d ∈ G.districtsOn D := ADMG.mem_districtsOn.2 ⟨y, hyD, rfl⟩
  have hdD : d ⊆ D := ADMG.subset_of_mem_districtsOn hd
  have hyd : y ∈ d := ADMG.mem_districtFinset.2 (ADMG.mem_district_self y)
  have hxd : x ∉ d := fun h => by
    have := (mem_sdiff.1 (ancIn_subset _ _ (hdD h))).2
    simp at this
  refine ⟨d, hd, insert x d, subset_univ _, ⟨ssubset_insert hxd, ?_, ?_⟩⟩
  · have hdc := biConnected_districtFinset (H := G) D y
    have hdT : d ⊆ insert x d := subset_insert x d
    have hxy' : ((G.restrict ↑(insert x d)).bidirected.Reachable x y) :=
      SimpleGraph.Adj.reachable ⟨hb, by simp, by simp [hyd]⟩
    have key : ∀ u ∈ insert x d, (G.restrict ↑(insert x d)).bidirected.Reachable u y := by
      intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · exact hxy'
      · exact reachable_restrict_mono hdT (hdc u hu y hyd)
    exact fun u hu v hv => (key u hu).trans (key v hv).symm
  · refine Subset.antisymm (ancIn_subset _ _) fun v hv => ?_
    rcases mem_insert.1 hv with rfl | hv
    · exact ancIn_closed (mem_insert_self _ _)
        (subset_ancIn (subset_insert _ _) hyd) hxy
    · exact subset_ancIn (subset_insert _ _) hv

include hxy hb in
/-- The algorithm also fails on the latent projection of the canonical DAG
(`ADMG.latentProjection_canonicalDAG`), with the copied sets. -/
theorem idAlg_canonical_eq_none (ord' : V ⊕ V × V → ℕ) :
    idAlg (G.embed Function.Embedding.inl) ord' ADMG.canonicalObs {.inl x} {.inl y} = none := by
  have := (ADMG.idAlg_canonical_eq_none_iff G ord' (fun _ => 0) univ {x} {y}).2
    (idAlg_eq_none hxy hb _)
  rw [map_singleton, map_singleton] at this
  exact this

include hG hxy hb in
/-- **The algorithm decides identifiability for a bow.** On the canonical DAG of an acyclic `G`
with `x → y` and `x ↔ y`, with every vertex of `G` observed, the effect of `x` on `y` is
identifiable at every configuration, within the class of models with a strictly positive
observed law, if and only if the algorithm succeeds on the latent projection. Both sides are
false. -/
theorem identifiableFrom_iff (ord' : V ⊕ V × V → ℕ) :
    (∀ w, SCM.IdentifiableFrom
      {m : SCM.Model G.canonicalDAG (fun _ => Bool) |
        ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
      (fun m => m.scm.effect {.inl x} w {.inl y} w)) ↔
      (idAlg (G.embed Function.Embedding.inl) ord' ADMG.canonicalObs {.inl x} {.inl y}).isSome
    := by
  rw [idAlg_canonical_eq_none hxy hb]
  exact ⟨fun h => absurd (h fun _ => true) (not_identifiableFrom hG hxy hb _),
    fun h => absurd h (by simp)⟩

/-! ### The bow itself -/

/-- The bow ADMG on `Fin 2`: `X = 0 → Y = 1` and `X ↔ Y`. -/
def bow2 : ADMG (Fin 2) := IDExamples.mixed [(0, 1)] [(0, 1)]

instance : DecidableRel bow2.directed.Adj :=
  inferInstanceAs (DecidableRel (IDExamples.mixed _ _).directed.Adj)
instance : DecidableRel bow2.bidirected.Adj :=
  inferInstanceAs (DecidableRel (IDExamples.mixed _ _).bidirected.Adj)

/-- The bow ADMG is acyclic. -/
theorem bow2_isAcyclic : bow2.IsAcyclic :=
  Digraph.isAcyclic_of_adj_lt (fun v : Fin 2 => v.val) fun u v h => by
    revert u v h
    decide

/-- **The bow as an instance.** On the canonical DAG of the bow `X → Y`, `X ↔ Y`, the effect of
`X` on `Y` is identifiable at every configuration, within the class of models with a strictly
positive observed law, if and only if the algorithm succeeds on the latent projection. -/
theorem bow2_identifiableFrom_iff (ord' : Fin 2 ⊕ Fin 2 × Fin 2 → ℕ) :
    (∀ w, SCM.IdentifiableFrom
      {m : SCM.Model bow2.canonicalDAG (fun _ => Bool) |
        ∀ w, 0 < m.scm.dist.margAt ADMG.canonicalObs w} ADMG.canonicalObs
      (fun m => m.scm.effect {.inl 0} w {.inl 1} w)) ↔
      (idAlg (bow2.embed Function.Embedding.inl) ord' ADMG.canonicalObs {.inl 0} {.inl 1}).isSome
    :=
  identifiableFrom_iff (x := 0) (y := 1) bow2_isAcyclic (by decide) (by decide) ord'

end IDCompletenessBow

end CausalInference
