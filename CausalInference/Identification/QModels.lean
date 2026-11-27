/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.SCM.Effects
public import CausalInference.SCM.Markov

/-!
# Boolean models with rational kernels

Concrete structural causal models on a graph over `Fin n` with Boolean values, whose kernels are
Bernoulli laws with rational success probabilities. The joint law, its marginals and the causal
effects of such a model are casts of rational numbers computed by finite sums and products, so
they can be evaluated exactly by `decide`.

## Main definitions

* `QModel.model G θ hθ hG`: the response-function model (`Digraph.MarkovKernels.toSCM`) whose
  kernel at `v` is the Bernoulli law with success probability `θ v x`, where `x` is the parent
  configuration with every non-parent set to `false`.
* `QModel.qjoint`, `QModel.qmarg`, `QModel.qeffect`: the rational joint mass, marginal masses
  and causal effects.

## Main results

* `QModel.margAt_model`, `QModel.effect_model`: the real marginal masses and effects are the
  casts of the rational ones.
* `QModel.margAt_model_pos`: if every `θ v x` lies strictly between `0` and `1`, every marginal
  mass of the model is strictly positive.
-/

@[expose] public section

namespace CausalInference

namespace QModel

open Finset

/-- The mass of the Boolean value `b` under the Bernoulli law with success probability `p`. -/
def bernQ (p : ℚ) (b : Bool) : ℚ := if b then p else 1 - p

/-- A Bernoulli mass with success probability strictly between `0` and `1` is positive. -/
theorem bernQ_pos {p : ℚ} (h₀ : 0 < p) (h₁ : p < 1) (b : Bool) : 0 < bernQ p b := by
  cases b
  · simp only [bernQ, Bool.false_eq_true, ↓reduceIte]
    linarith
  · simpa [bernQ] using h₀

variable {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]

/-- The configuration `x` with every vertex that is not a parent of `v` set to `false`. -/
def maskP (v : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun u => if u ∈ G.parentsFinset v then x u else false

/-- A parent configuration of `v`, extended by `false` outside the parents. -/
def extendP (v : Fin n) (z : G.parentsFinset v → Bool) : Fin n → Bool :=
  fun u => if h : u ∈ G.parentsFinset v then z ⟨u, h⟩ else false

/-- Extending the restriction of `x` to the parents gives the masked configuration. -/
theorem extendP_restrict (v : Fin n) (x : Fin n → Bool) :
    extendP G v ((G.parentsFinset v).restrict x) = maskP G v x := by
  funext u
  unfold extendP maskP
  split_ifs <;> rfl

variable (θ : Fin n → (Fin n → Bool) → ℚ) (hθ : ∀ v x, 0 < θ v x ∧ θ v x < 1)

/-- The Markov kernels with Bernoulli laws of success probability `θ v x` at the masked parent
configuration `x`. -/
noncomputable def kernels : G.MarkovKernels (fun _ => Bool) where
  kernel v z b := (bernQ (θ v (extendP G v z)) b : ℝ)
  nonneg v z b :=
    Rat.cast_nonneg.2 (bernQ_pos (hθ v _).1 (hθ v _).2 b).le
  sum_eq_one v z := by
    simp only [Fintype.sum_bool, bernQ, ↓reduceIte, Bool.false_eq_true]
    push_cast
    ring

/-- The response-function structural causal model realizing `QModel.kernels`. -/
noncomputable def model (hG : G.IsAcyclic) :
    SCM G (fun _ => Bool) (fun v => (G.parentsFinset v → Bool) → Bool) :=
  (kernels G θ hθ).toSCM hG

/-- The rational joint mass. -/
def qjoint (x : Fin n → Bool) : ℚ := ∏ v, bernQ (θ v (maskP G v x)) (x v)

/-- The rational marginal mass on `S` at `w`. -/
def qmarg (S : Finset (Fin n)) (w : Fin n → Bool) : ℚ :=
  ∑ x ∈ FiniteDist.agreeOn S w, qjoint G θ x

/-- The rational mass of `y` under the intervention `do(X := xv)` (truncated factorization). -/
def qint (X : Finset (Fin n)) (xv y : Fin n → Bool) : ℚ :=
  if ∀ v ∈ X, y v = xv v then ∏ v ∈ Xᶜ, bernQ (θ v (maskP G v y)) (y v) else 0

/-- The rational causal effect `P(Y = yv_Y | do(X := xv_X))`. -/
def qeffect (X : Finset (Fin n)) (xv : Fin n → Bool) (Y : Finset (Fin n)) (yv : Fin n → Bool) :
    ℚ :=
  ∑ y ∈ FiniteDist.agreeOn Y yv, qint G θ X xv y

variable (hG : G.IsAcyclic)

/-- The factor of `v` in the model is the rational Bernoulli mass at the masked configuration. -/
theorem factor_model (v : Fin n) (x : Fin n → Bool) :
    (model G θ hθ hG).kernels.factor v x = (bernQ (θ v (maskP G v x)) (x v) : ℝ) := by
  change (Digraph.MarkovKernels.toSCM (kernels G θ hθ) hG).kernel v _ (x v) = _
  rw [Digraph.MarkovKernels.kernel_toSCM]
  change (bernQ (θ v (extendP G v _)) (x v) : ℝ) = _
  rw [extendP_restrict]

/-- The joint law of the model is the cast of the rational joint mass. -/
theorem dist_model (x : Fin n → Bool) : (model G θ hθ hG).dist x = (qjoint G θ x : ℝ) := by
  rw [SCM.dist_eq_prod]
  simp only [factor_model, qjoint]
  push_cast
  rfl

/-- The marginal masses of the model are the casts of the rational ones. -/
theorem margAt_model (S : Finset (Fin n)) (w : Fin n → Bool) :
    (model G θ hθ hG).dist.margAt S w = (qmarg G θ S w : ℝ) := by
  unfold qmarg FiniteDist.margAt FiniteDist.prob
  push_cast
  exact sum_congr rfl fun x _ => dist_model G θ hθ hG x

/-- The causal effects of the model are the casts of the rational ones, computed by the
truncated factorization. -/
theorem effect_model (X : Finset (Fin n)) (xv : Fin n → Bool) (Y : Finset (Fin n))
    (yv : Fin n → Bool) :
    (model G θ hθ hG).effect X xv Y yv = (qeffect G θ X xv Y yv : ℝ) := by
  unfold SCM.effect qeffect FiniteDist.margAt FiniteDist.prob
  push_cast
  refine sum_congr rfl fun y _ => ?_
  rw [SCM.dist_intervene, qint]
  split_ifs
  · push_cast
    exact prod_congr rfl fun v _ => factor_model G θ hθ hG v y
  · simp

include hθ in
/-- The rational joint mass is strictly positive. -/
theorem qjoint_pos (x : Fin n → Bool) : 0 < qjoint G θ x :=
  prod_pos fun v _ => bernQ_pos (hθ v _).1 (hθ v _).2 _

/-- **Positivity**: every marginal mass of the model is strictly positive. -/
theorem margAt_model_pos (S : Finset (Fin n)) (w : Fin n → Bool) :
    0 < (model G θ hθ hG).dist.margAt S w := by
  rw [margAt_model]
  exact_mod_cast (qjoint_pos G θ hθ w).trans_le
    (single_le_sum (fun x _ => (qjoint_pos G θ hθ x).le) (FiniteDist.mem_agreeOn_self S w))

end QModel

end CausalInference
