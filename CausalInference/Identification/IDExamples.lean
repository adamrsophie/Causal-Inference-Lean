/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDSoundness

/-!
# The identification algorithm on standard graphs

Runs of the identification algorithm `idAlg` on small graphs, each checked in Lean.

* **Front door** (Pearl 2009, section 3.3.2, Figure 3.5 with the latent made explicit): on the
  graph `X → Z → Y` with a latent common cause `U` of `X` and `Y`, the algorithm succeeds and its
  expression evaluates, under every law, to the front-door formula
  `∑_z P(z | x) ∑_x' P(y | x', z) P(x')` in the form of `SCM.effect_eq_sum_of_frontDoor`
  (`IDExamples.frontDoor_idAlg`).
* **Back door** (Pearl 2009, section 3.3.1): on `Z → X → Y`, `Z → Y` with every vertex
  observed, it returns the adjustment formula `∑_z P(y | x, z) P(z)` in the form of
  `SCM.effect_eq_sum_of_backDoor` (`IDExamples.backDoor_idAlg`).
* **Bow** (Pearl 2009, Figure 3.7(a)): on `X → Y` with a latent common cause of `X` and `Y`, it
  fails (`IDExamples.bow_idAlg`). For the same graph, observed set and class of models (strictly
  positive observed law) as in the soundness theorem `SCM.identifiableFrom_of_idAlg`, the effect
  is not identifiable (`SCM.BowExample.not_identifiableFrom_effect`); `IDExamples.bow_link`
  states both together.

The latent projections of the example DAGs are computed with `latentProjection_of_roots`: when
every latent vertex is a root, the projection keeps the edges between observed vertices and
joins two observed vertices by a bidirected edge when they share a latent parent.
-/

@[expose] public section

namespace CausalInference

open Finset

/-! ### Latent projection when the latent vertices are roots -/

section Roots

variable {V : Type*} {D : Digraph V} {O : Finset V}

/-- When no latent vertex has a parent, a directed path with latent interior is a single edge. -/
theorem latentPath_iff_of_roots (hroot : ∀ l ∉ O, ∀ u, ¬ D.Adj u l) {a b : V} :
    LatentPath D (↑O)ᶜ a b ↔ D.Adj a b := by
  refine ⟨fun ⟨w, haw, hwb⟩ => ?_, latentPath_of_adj⟩
  rcases haw.cases_head with rfl | ⟨c, hac, -⟩
  · exact hwb
  · exact absurd hac.1 (hroot c hac.2 a)

/-- With root latent vertices, the directed edges of the latent projection are the edges of `D`
between observed vertices. -/
theorem latentProjection_directed_adj_of_roots (hroot : ∀ l ∉ O, ∀ u, ¬ D.Adj u l) {u v : V} :
    (latentProjection D (↑O)ᶜ).directed.Adj u v ↔ u ∈ O ∧ v ∈ O ∧ D.Adj u v := by
  rw [latentProjection_directed_adj, latentPath_iff_of_roots hroot]
  simp

/-- With root latent vertices, the bidirected edges of the latent projection join two distinct
observed vertices with a common latent parent. -/
theorem latentProjection_bidirected_adj_of_roots (hroot : ∀ l ∉ O, ∀ u, ¬ D.Adj u l)
    {u v : V} :
    (latentProjection D (↑O)ᶜ).bidirected.Adj u v ↔
      u ≠ v ∧ u ∈ O ∧ v ∈ O ∧ ∃ l ∉ O, D.Adj l u ∧ D.Adj l v := by
  rw [latentProjection_bidirected_adj]
  simp only [latentPath_iff_of_roots hroot]
  simp

end Roots

namespace IDExamples

/-! ### Graphs from edge lists -/

/-- The directed graph on `Fin n` with the listed edges. -/
def edges {n : ℕ} (d : List (Fin n × Fin n)) : Digraph (Fin n) where
  Adj i j := (i, j) ∈ d

instance {n : ℕ} (d : List (Fin n × Fin n)) : DecidableRel (edges d).Adj :=
  fun i j => inferInstanceAs (Decidable ((i, j) ∈ d))

/-- The mixed graph on `Fin n` with the listed directed edges `d` and bidirected edges `b`. -/
def mixed {n : ℕ} (d b : List (Fin n × Fin n)) : ADMG (Fin n) :=
  ⟨edges d, SimpleGraph.fromRel fun i j => (i, j) ∈ b⟩

instance {n : ℕ} (d b : List (Fin n × Fin n)) : DecidableRel (mixed d b).directed.Adj :=
  inferInstanceAs (DecidableRel (edges d).Adj)

instance {n : ℕ} (d b : List (Fin n × Fin n)) : DecidableRel (mixed d b).bidirected.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ((i, j) ∈ b ∨ (j, i) ∈ b)))

/-- The directed edges of `mixed d b` are the pairs in `d`. -/
theorem mixed_directed_adj {n : ℕ} (d b : List (Fin n × Fin n)) (i j : Fin n) :
    (mixed d b).directed.Adj i j ↔ (i, j) ∈ d := Iff.rfl

/-- The bidirected edges of `mixed d b` are the pairs in `b`, in either direction. -/
theorem mixed_bidirected_adj {n : ℕ} (d b : List (Fin n × Fin n)) (i j : Fin n) :
    (mixed d b).bidirected.Adj i j ↔ i ≠ j ∧ ((i, j) ∈ b ∨ (j, i) ∈ b) := Iff.rfl

/-- The order of `Fin n` by value. -/
def ordFin {n : ℕ} (v : Fin n) : ℕ := v.val

/-- The order by value is injective. -/
theorem ordFin_injective {n : ℕ} : Function.Injective (ordFin (n := n)) :=
  fun _ _ h => Fin.ext h

/-! ### Evaluation helpers -/

section Eval

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)] (p : FiniteDist (∀ v, α v))

/-- Tian's formula applied to the observed law: the product of the conditionals
`P(o^{≤v}) / P(o^{<v})`. -/
theorem eval_tianExpr_marg (ord : V → ℕ) (O S : Finset V) (w : ∀ v, α v) :
    (tianExpr ord O S (.marg O)).eval p w = ∏ v ∈ S,
      p.margAt (O.filter fun u => ord u ≤ ord v) w /
        p.margAt (O.filter fun u => ord u < ord v) w := by
  simp only [tianExpr, IdExpr.eval_prodV, IdExpr.eval_div, IdExpr.eval_sum, IdExpr.eval_marg]
  refine prod_congr rfl fun v _ => ?_
  rw [FiniteDist.sum_agreeOn_margAt _ sdiff_subset, FiniteDist.sum_agreeOn_margAt _ sdiff_subset,
    Finset.sdiff_sdiff_eq_self (filter_subset _ O), Finset.sdiff_sdiff_eq_self (filter_subset _ O)]

end Eval

/-! ### The front-door graph -/

/-- The front-door DAG on `Fin 4`: `X = 0 → Z = 1 → Y = 2`, and a latent `U = 3` with
`U → X` and `U → Y`. -/
def fdDAG : Digraph (Fin 4) := edges [(0, 1), (1, 2), (3, 0), (3, 2)]

instance : DecidableRel fdDAG.Adj := inferInstanceAs (DecidableRel (edges _).Adj)

/-- The front-door ADMG: `X → Z → Y` and `X ↔ Y`; the latent vertex `3` is isolated. -/
def fdH : ADMG (Fin 4) := mixed [(0, 1), (1, 2)] [(0, 2)]

instance : DecidableRel fdH.directed.Adj := inferInstanceAs (DecidableRel (mixed _ _).directed.Adj)
instance : DecidableRel fdH.bidirected.Adj :=
  inferInstanceAs (DecidableRel (mixed _ _).bidirected.Adj)

/-- The latent projection of the front-door DAG onto `{X, Z, Y}` is the front-door ADMG. -/
theorem fdDAG_projection : latentProjection fdDAG (↑({0, 1, 2} : Finset (Fin 4)))ᶜ = fdH := by
  have hroot : ∀ l ∉ ({0, 1, 2} : Finset (Fin 4)), ∀ u, ¬ fdDAG.Adj u l := by decide
  ext u v
  · rw [latentProjection_directed_adj_of_roots hroot]
    revert u v
    decide
  · rw [latentProjection_bidirected_adj_of_roots hroot]
    revert u v
    decide

/-- `ordFin` is a topological order of the front-door ADMG. -/
theorem fdH_ord : ∀ u v, fdH.directed.Adj u v → ordFin u < ordFin v := by decide

/-- **The algorithm on the front-door graph**: it succeeds, and its expression evaluates under
every joint law `p` to the front-door formula
`∑_z P(z, x) / P(x) * ∑_x' P(y, z, x') / P(z, x') * P(x')`, exactly the right side of
`SCM.effect_eq_sum_of_frontDoor` for `X = {0}`, `Y = {2}`, `Z = {1}`. -/
theorem frontDoor_idAlg : ∃ e, idAlg fdH ordFin {0, 1, 2} {0} {2} = some e ∧
    ∀ {α : Fin 4 → Type} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
      (p : FiniteDist (∀ v, α v)) (w : ∀ v, α v),
      e.eval p w = ∑ c ∈ FiniteDist.agreeOn ({1} : Finset (Fin 4))ᶜ w,
        p.margAt ({1} ∪ {0}) c / p.margAt {0} c *
          ∑ d ∈ FiniteDist.agreeOn ({0} : Finset (Fin 4))ᶜ c,
            p.margAt ({2} ∪ {1} ∪ {0}) d / p.margAt ({1} ∪ {0}) d * p.margAt {0} d := by
  have hD : ancIn fdH ({0, 1, 2} \ {0}) {2} = {1, 2} := by decide
  have hDs : fdH.districtsOn {1, 2} = {{1}, {2}} := by decide
  have hp1 : idPart fdH ordFin {0, 1, 2} {1} =
      some (.sum ∅ (tianExpr ordFin {0, 1, 2} {1} (.marg {0, 1, 2}))) := by
    rw [idPart, show closeIn fdH {0, 1, 2} {1} = {1} by decide,
      identify_of_eq _ _ _ (by decide), sdiff_self, bot_eq_empty]
  have hp2 : idPart fdH ordFin {0, 1, 2} {2} =
      some (.sum {0} (tianExpr ordFin {0, 1, 2} {0, 2} (.marg {0, 1, 2}))) := by
    rw [idPart, show closeIn fdH {0, 1, 2} {2} = {0, 2} by decide,
      identify_of_eq _ _ _ (by decide), show ({0, 2} \ {2} : Finset (Fin 4)) = {0} by decide]
  refine ⟨_, idAlg_eq_some fdH ordFin ⟨by decide, by decide⟩ ?_, ?_⟩
  · rw [hD, hDs]
    simp [hp1, hp2]
  · intro α _ _ p w
    rw [IdExpr.eval_sum, hD, hDs, show ({1, 2} \ {2} : Finset (Fin 4)) = {1} by decide]
    refine sum_congr rfl fun c _ => ?_
    rw [IdExpr.eval_prodSets, prod_pair (by decide), hp1, hp2]
    simp only [Option.getD_some, IdExpr.eval_sum, FiniteDist.sum_agreeOn_compl_empty,
      eval_tianExpr_marg, prod_singleton]
    rw [show ((({0, 1, 2} : Finset (Fin 4)).filter fun u => ordFin u ≤ ordFin 1)) = {0, 1} by
        decide,
      show ((({0, 1, 2} : Finset (Fin 4)).filter fun u => ordFin u < ordFin 1)) = {0} by decide,
      show ({1} ∪ {0} : Finset (Fin 4)) = {0, 1} by decide,
      show ({2} ∪ {1} ∪ {0} : Finset (Fin 4)) = {0, 1, 2} by decide]
    congr 1
    refine sum_congr rfl fun d _ => ?_
    rw [prod_pair (by decide),
      show ((({0, 1, 2} : Finset (Fin 4)).filter fun u => ordFin u ≤ ordFin 0)) = {0} by decide,
      show ((({0, 1, 2} : Finset (Fin 4)).filter fun u => ordFin u < ordFin 0)) = ∅ by decide,
      show ((({0, 1, 2} : Finset (Fin 4)).filter fun u => ordFin u ≤ ordFin 2)) = {0, 1, 2} by
        decide,
      show ((({0, 1, 2} : Finset (Fin 4)).filter fun u => ordFin u < ordFin 2)) = {0, 1} by
        decide,
      FiniteDist.margAt_empty]
    ring

/-! ### A back-door graph with an observed confounder -/

/-- The back-door DAG on `Fin 3`: `Z = 0 → X = 1 → Y = 2` and `Z → Y`, every vertex observed. -/
def bdDAG : Digraph (Fin 3) := edges [(0, 1), (1, 2), (0, 2)]

instance : DecidableRel bdDAG.Adj := inferInstanceAs (DecidableRel (edges _).Adj)

/-- The back-door graph as an ADMG, with no bidirected edge. -/
def bdH : ADMG (Fin 3) := mixed [(0, 1), (1, 2), (0, 2)] []

instance : DecidableRel bdH.directed.Adj := inferInstanceAs (DecidableRel (mixed _ _).directed.Adj)
instance : DecidableRel bdH.bidirected.Adj :=
  inferInstanceAs (DecidableRel (mixed _ _).bidirected.Adj)

/-- The latent projection of the back-door DAG onto all its vertices is the back-door ADMG. -/
theorem bdDAG_projection : latentProjection bdDAG (↑({0, 1, 2} : Finset (Fin 3)))ᶜ = bdH := by
  have hroot : ∀ l ∉ ({0, 1, 2} : Finset (Fin 3)), ∀ u, ¬ bdDAG.Adj u l := by decide
  ext u v
  · rw [latentProjection_directed_adj_of_roots hroot]
    revert u v
    decide
  · rw [latentProjection_bidirected_adj_of_roots hroot]
    revert u v
    decide

/-- `ordFin` is a topological order of the back-door graph. -/
theorem bdH_ord : ∀ u v, bdH.directed.Adj u v → ordFin u < ordFin v := by decide

/-- **The algorithm on the back-door graph**: it succeeds, and its expression evaluates under
every joint law `p` to the adjustment formula `∑_z P(y, x, z) / P(x, z) * P(z)`, exactly the
right side of `SCM.effect_eq_sum_of_backDoor` for `X = {1}`, `Y = {2}`, `Z = {0}`. -/
theorem backDoor_idAlg : ∃ e, idAlg bdH ordFin {0, 1, 2} {1} {2} = some e ∧
    ∀ {α : Fin 3 → Type} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
      (p : FiniteDist (∀ v, α v)) (w : ∀ v, α v),
      e.eval p w = ∑ c ∈ FiniteDist.agreeOn ({0} : Finset (Fin 3))ᶜ w,
        p.margAt ({2} ∪ {1} ∪ {0}) c / p.margAt ({1} ∪ {0}) c * p.margAt {0} c := by
  have hD : ancIn bdH ({0, 1, 2} \ {1}) {2} = {0, 2} := by decide
  have hDs : bdH.districtsOn {0, 2} = {{0}, {2}} := by decide
  have hp0 : idPart bdH ordFin {0, 1, 2} {0} =
      some (.sum ∅ (tianExpr ordFin {0, 1, 2} {0} (.marg {0, 1, 2}))) := by
    rw [idPart, show closeIn bdH {0, 1, 2} {0} = {0} by decide,
      identify_of_eq _ _ _ (by decide), sdiff_self, bot_eq_empty]
  have hp2 : idPart bdH ordFin {0, 1, 2} {2} =
      some (.sum ∅ (tianExpr ordFin {0, 1, 2} {2} (.marg {0, 1, 2}))) := by
    rw [idPart, show closeIn bdH {0, 1, 2} {2} = {2} by decide,
      identify_of_eq _ _ _ (by decide), sdiff_self, bot_eq_empty]
  refine ⟨_, idAlg_eq_some bdH ordFin ⟨by decide, by decide⟩ ?_, ?_⟩
  · rw [hD, hDs]
    simp [hp0, hp2]
  · intro α _ _ p w
    rw [IdExpr.eval_sum, hD, hDs, show ({0, 2} \ {2} : Finset (Fin 3)) = {0} by decide]
    refine sum_congr rfl fun c _ => ?_
    rw [IdExpr.eval_prodSets, prod_pair (by decide), hp0, hp2]
    simp only [Option.getD_some, IdExpr.eval_sum, FiniteDist.sum_agreeOn_compl_empty,
      eval_tianExpr_marg, prod_singleton]
    rw [show ((({0, 1, 2} : Finset (Fin 3)).filter fun u => ordFin u ≤ ordFin 0)) = {0} by
        decide,
      show ((({0, 1, 2} : Finset (Fin 3)).filter fun u => ordFin u < ordFin 0)) = ∅ by decide,
      show ((({0, 1, 2} : Finset (Fin 3)).filter fun u => ordFin u ≤ ordFin 2)) = {0, 1, 2} by
        decide,
      show ((({0, 1, 2} : Finset (Fin 3)).filter fun u => ordFin u < ordFin 2)) = {0, 1} by
        decide,
      show ({2} ∪ {1} ∪ {0} : Finset (Fin 3)) = {0, 1, 2} by decide,
      show ({1} ∪ {0} : Finset (Fin 3)) = {0, 1} by decide, FiniteDist.margAt_empty]
    ring

/-! ### The bow graph -/

/-- The bow ADMG on `Fin 3`: `X = 1 → Y = 2` and `X ↔ Y`; the latent vertex `0` is isolated. -/
def bowH : ADMG (Fin 3) := mixed [(1, 2)] [(1, 2)]

instance : DecidableRel bowH.directed.Adj :=
  inferInstanceAs (DecidableRel (mixed _ _).directed.Adj)
instance : DecidableRel bowH.bidirected.Adj :=
  inferInstanceAs (DecidableRel (mixed _ _).bidirected.Adj)

/-- The latent projection of the bow DAG of `SCM.BowExample` (latent `U = 0`, edges `U → X`,
`U → Y`, `X → Y`) onto `{X, Y}` is the bow ADMG. -/
theorem bow_projection :
    latentProjection SCM.BowExample.bow (↑({1, 2} : Finset (Fin 3)))ᶜ = bowH := by
  have hroot : ∀ l ∉ ({1, 2} : Finset (Fin 3)), ∀ u, ¬ SCM.BowExample.bow.Adj u l := by decide
  ext u v
  · rw [latentProjection_directed_adj_of_roots hroot]
    revert u v
    decide
  · rw [latentProjection_bidirected_adj_of_roots hroot]
    revert u v
    decide

/-- **The algorithm fails on the bow graph**: the ancestral closure of `Y` inside the district
`{X, Y}` is the whole district. -/
theorem bow_idAlg : idAlg bowH ordFin {1, 2} {1} {2} = none := by
  refine idAlg_eq_none bowH ordFin (d := {2}) (by decide) ?_
  rw [idPart, show closeIn bowH {1, 2} {2} = {1, 2} by decide]
  exact identify_of_not _ _ _ (by decide) (by decide)

/-- **The failure on the bow graph agrees with non-identifiability.** The algorithm fails on the
bow ADMG, which is the latent projection of the bow DAG of `SCM.BowExample`; and for that DAG,
the observed set `{X, Y}` and the class of models with a strictly positive observed law (the
class of the soundness theorem `SCM.identifiableFrom_of_idAlg`), the effect
`P(Y = true | do(X = true))` is not identifiable (`SCM.BowExample.not_identifiableFrom_effect`).
So for this query the failure is no loss: no procedure identifies the effect from the observed
law within this class. -/
theorem bow_link :
    idAlg bowH ordFin {1, 2} {1} {2} = none ∧
      latentProjection SCM.BowExample.bow (↑({1, 2} : Finset (Fin 3)))ᶜ = bowH ∧
      ¬ SCM.IdentifiableFrom
        {m : SCM.Model SCM.BowExample.bow (fun _ => Bool) |
          ∀ w, 0 < m.scm.dist.margAt {1, 2} w}
        {1, 2} (fun m => m.scm.effect {1} SCM.BowExample.treat {2} SCM.BowExample.treat) :=
  ⟨bow_idAlg, bow_projection, SCM.BowExample.not_identifiableFrom_effect⟩

end IDExamples

end CausalInference
