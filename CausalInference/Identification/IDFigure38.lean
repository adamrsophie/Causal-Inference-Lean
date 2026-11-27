/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDExamples
public import CausalInference.Graphical.Criteria.BackDoor
public import CausalInference.Graphical.Criteria.FrontDoor

/-!
# A graph identifiable by neither the back-door nor the front-door criterion

The graph of Pearl (2009), Figure 3.8(f): observed `X = 0`, `Z₁ = 1`, `Z₂ = 2`, `Y = 3`, edges
`X → Z₁`, `X → Y`, `Z₁ → Z₂`, `Z₁ → Y`, `Z₂ → Y`, and two confounding arcs `X ↔ Z₂`, `Z₁ ↔ Y`,
made explicit by latent vertices `4` (a parent of `X` and `Z₂`) and `5` (a parent of `Z₁` and
`Y`). Pearl derives (equation (3.48))
`P(y | do(x)) = ∑_{z₁, z₂} P(y | z₁, z₂, x) P(z₁ | x) ∑_{x'} P(z₂ | z₁, x') P(x')`.

## Main results

* `IDFigure38.no_backDoor_no_frontDoor`, `IDFigure38.no_backDoorAdjustment`: no set of observed
  vertices satisfies the back-door criterion or the front-door criterion for the effect of `X`
  on `Y`.
* `IDFigure38.fig38_idAlg`: the identification algorithm succeeds, and its expression evaluates
  under every law to the formula (3.48).
* `IDFigure38.effect_eq_formula`: hence, for every model on the graph with a strictly positive
  observed law, `P(y | do(x))` equals the formula (3.48), by the soundness theorem
  `SCM.effect_eq_eval_of_idAlg`.
-/

@[expose] public section

namespace CausalInference

namespace IDFigure38

open Finset IDExamples

/-- The DAG of Figure 3.8(f) with the two latent vertices `4` and `5` made explicit. -/
def fig38DAG : Digraph (Fin 6) :=
  edges [(0, 1), (0, 3), (1, 2), (1, 3), (2, 3), (4, 0), (4, 2), (5, 1), (5, 3)]

instance : DecidableRel fig38DAG.Adj := inferInstanceAs (DecidableRel (edges _).Adj)

/-- The observed vertices `X, Z₁, Z₂, Y`. -/
def obs : Finset (Fin 6) := {0, 1, 2, 3}

/-- The ADMG of Figure 3.8(f): the edges between observed vertices and the arcs `X ↔ Z₂`,
`Z₁ ↔ Y`. -/
def fig38H : ADMG (Fin 6) := mixed [(0, 1), (0, 3), (1, 2), (1, 3), (2, 3)] [(0, 2), (1, 3)]

instance : DecidableRel fig38H.directed.Adj :=
  inferInstanceAs (DecidableRel (mixed _ _).directed.Adj)
instance : DecidableRel fig38H.bidirected.Adj :=
  inferInstanceAs (DecidableRel (mixed _ _).bidirected.Adj)

/-- The latent projection of the DAG onto the observed vertices is the ADMG of Figure 3.8(f). -/
theorem fig38_projection : latentProjection fig38DAG (↑obs)ᶜ = fig38H := by
  have hroot : ∀ l ∉ obs, ∀ u, ¬ fig38DAG.Adj u l := by decide
  ext u v
  · rw [latentProjection_directed_adj_of_roots hroot]
    revert u v
    decide
  · rw [latentProjection_bidirected_adj_of_roots hroot]
    revert u v
    decide

/-- `ordFin` is a topological order of the ADMG. -/
theorem fig38H_ord : ∀ u v, fig38H.directed.Adj u v → ordFin u < ordFin v := by decide

/-- **Neither criterion applies**: for every set `Z` of observed vertices, `Z` satisfies neither
the back-door criterion nor the front-door criterion for the effect of `X = 0` on `Y = 3` in the
DAG. -/
theorem no_backDoor_no_frontDoor : ∀ Z ∈ obs.powerset,
    ¬ fig38DAG.BackDoor {0} {3} {v | v ∈ Z} ∧ ¬ fig38DAG.FrontDoor {0} {3} {v | v ∈ Z} := by
  decide +kernel

/-- In particular no set of observed vertices is a back-door adjustment set (the form of the
criterion used by `SCM.effect_eq_sum_of_backDoor`). -/
theorem no_backDoorAdjustment : ∀ Z ∈ obs.powerset,
    ¬ fig38DAG.BackDoorAdjustment {0} {3} {v | v ∈ Z} :=
  fun Z hZ h => (no_backDoor_no_frontDoor Z hZ).1 h.1

/-- **The algorithm on Figure 3.8(f)**: it succeeds, and its expression evaluates under every
joint law `p` to Pearl's formula (3.48),
`∑_{z₁, z₂} P(y, z₂, z₁, x) / P(z₂, z₁, x) * P(z₁, x) / P(x) *`
`∑_x' P(z₂, z₁, x') / P(z₁, x') * P(x')`. -/
theorem fig38_idAlg : ∃ e, idAlg fig38H ordFin obs {0} {3} = some e ∧
    ∀ {α : Fin 6 → Type} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
      (p : FiniteDist (∀ v, α v)) (w : ∀ v, α v),
      e.eval p w = ∑ c ∈ FiniteDist.agreeOn ({1, 2} : Finset (Fin 6))ᶜ w,
        p.margAt {0, 1, 2, 3} c / p.margAt {0, 1, 2} c * (p.margAt {0, 1} c / p.margAt {0} c) *
          ∑ d ∈ FiniteDist.agreeOn ({0} : Finset (Fin 6))ᶜ c,
            p.margAt {0, 1, 2} d / p.margAt {0, 1} d * p.margAt {0} d := by
  have hD : ancIn fig38H (obs \ {0}) {3} = {1, 2, 3} := by decide
  have hDs : fig38H.districtsOn {1, 2, 3} = {{1, 3}, {2}} := by decide
  have hp13 : idPart fig38H ordFin obs {1, 3} =
      some (.sum ∅ (tianExpr ordFin obs {1, 3} (.marg obs))) := by
    rw [idPart, show closeIn fig38H obs {1, 3} = {1, 3} by decide,
      identify_of_eq _ _ _ (by decide), sdiff_self, bot_eq_empty]
  have hp2 : idPart fig38H ordFin obs {2} =
      some (.sum {0} (tianExpr ordFin obs {0, 2} (.marg obs))) := by
    rw [idPart, show closeIn fig38H obs {2} = {0, 2} by decide,
      identify_of_eq _ _ _ (by decide), show ({0, 2} \ {2} : Finset (Fin 6)) = {0} by decide]
  refine ⟨_, idAlg_eq_some fig38H ordFin ⟨by decide, by decide⟩ ?_, ?_⟩
  · rw [hD, hDs]
    simp [hp13, hp2]
  · intro α _ _ p w
    rw [IdExpr.eval_sum, hD, hDs, show ({1, 2, 3} \ {3} : Finset (Fin 6)) = {1, 2} by decide]
    refine sum_congr rfl fun c _ => ?_
    rw [IdExpr.eval_prodSets, prod_pair (by decide), hp13, hp2]
    simp only [Option.getD_some, IdExpr.eval_sum, FiniteDist.sum_agreeOn_compl_empty,
      eval_tianExpr_marg]
    rw [prod_pair (by decide),
      show ((obs.filter fun u => ordFin u ≤ ordFin 1)) = {0, 1} by decide,
      show ((obs.filter fun u => ordFin u < ordFin 1)) = {0} by decide,
      show ((obs.filter fun u => ordFin u ≤ ordFin 3)) = {0, 1, 2, 3} by decide,
      show ((obs.filter fun u => ordFin u < ordFin 3)) = {0, 1, 2} by decide]
    congr 1
    · ring
    refine sum_congr rfl fun d _ => ?_
    rw [prod_pair (by decide),
      show ((obs.filter fun u => ordFin u ≤ ordFin 0)) = {0} by decide,
      show ((obs.filter fun u => ordFin u < ordFin 0)) = ∅ by decide,
      show ((obs.filter fun u => ordFin u ≤ ordFin 2)) = {0, 1, 2} by decide,
      show ((obs.filter fun u => ordFin u < ordFin 2)) = {0, 1} by decide,
      FiniteDist.margAt_empty]
    ring

/-- **The effect in Figure 3.8(f) is Pearl's formula (3.48)**: for every structural causal model
on the DAG with a strictly positive observed law, and every configuration `w`,
`P(Y = w_Y | do(X := w_X))` equals the formula of `fig38_idAlg` evaluated on the model's joint
law, by the soundness of the identification algorithm. -/
theorem effect_eq_formula {α : Fin 6 → Type} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    {ε : Fin 6 → Type*} [∀ v, Fintype (ε v)] (M : SCM fig38DAG α ε)
    (hpos : ∀ w, 0 < M.dist.margAt obs w) (w : ∀ v, α v) :
    M.effect {0} w {3} w = ∑ c ∈ FiniteDist.agreeOn ({1, 2} : Finset (Fin 6))ᶜ w,
      M.dist.margAt {0, 1, 2, 3} c / M.dist.margAt {0, 1, 2} c *
        (M.dist.margAt {0, 1} c / M.dist.margAt {0} c) *
        ∑ d ∈ FiniteDist.agreeOn ({0} : Finset (Fin 6))ᶜ c,
          M.dist.margAt {0, 1, 2} d / M.dist.margAt {0, 1} d * M.dist.margAt {0} d := by
  obtain ⟨e, he, heval⟩ := fig38_idAlg
  rw [M.effect_eq_eval_of_idAlg fig38_projection ordFin ordFin_injective.injOn fig38H_ord hpos
    he w, heval]

end IDFigure38

end CausalInference
