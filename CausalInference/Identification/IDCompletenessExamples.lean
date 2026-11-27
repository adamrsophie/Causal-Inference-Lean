/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.QModels
public import CausalInference.Identification.IDExamples
public import CausalInference.Identification.IDNonIdent
public import CausalInference.Identification.CFactor

/-!
# Failure of the identification algorithm and non-identifiability on examples

Boolean models whose kernels are Bernoulli laws with rational success probabilities in the
closed interval `[0, 1]`, so that a vertex may be a deterministic function of its parents (the
models of `CausalInference.Identification.QModels` need the open interval). Their marginals and
effects are casts of rational numbers, which `decide` evaluates; positivity of the observed law
is then checked directly instead of following from the kernels.

On two DAGs with one latent root per bidirected edge, with edges to its two endpoints, the
algorithm fails and the effect is not identifiable within the class of models with a strictly
positive observed law, the class of the soundness theorem
`SCM.identifiableFrom_of_idAlg`. So on these graphs, success of the algorithm is equivalent to
identifiability of the effect.

## Main definitions

* `QModel.detKernels`, `QModel.detModel`: the models with success probabilities in `[0, 1]`.

## Main results

* `QModel.not_identifiableFrom_of_qmarg_eq_of_pos`: the non-identifiability certificate for these
  models, with positivity of the observed marginal as a hypothesis.
* `IDCompletenessExamples.wit_not_identifiableFrom`: on the canonical DAG of `W → X → Y`,
  `W ↔ Y`, `X ↔ W`, the effect of `X` on `Y` is not identifiable. The two models are
  `W = a + b`, `X = W + b` (so `X = a`), and `Y = a + n` or `Y = X + n` (sums modulo two),
  with fair latent bits `a` (for `W ↔ Y`) and `b` (for `X ↔ W`) and an independent bit `n`
  with `P(n = 1) = 1/4`. They give the same observed law, which is strictly positive, and the
  effects `1/2` and `3/4`.
* `IDCompletenessExamples.wit_cFactor_not_identifiableFrom`: the c-factor `Q[{Y}]` is not
  identifiable either.
* `IDCompletenessExamples.wit_idAlg`: the algorithm fails on this graph.
* `IDCompletenessExamples.wit_iff`, `IDCompletenessExamples.bow_iff`: on this graph and on the
  bow graph, the effect is identifiable at every configuration if and only if the algorithm
  succeeds (both sides are false).
-/

@[expose] public section

namespace CausalInference

open Finset

namespace QModel

/-- A Bernoulli mass with success probability in `[0, 1]` is nonnegative. -/
theorem bernQ_nonneg {p : ℚ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1) (b : Bool) : 0 ≤ bernQ p b := by
  cases b
  · simp only [bernQ, Bool.false_eq_true, ↓reduceIte]
    linarith
  · simpa [bernQ] using h₀

variable {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]
  (θ : Fin n → (Fin n → Bool) → ℚ) (hθ : ∀ v x, 0 ≤ θ v x ∧ θ v x ≤ 1)

/-- The Markov kernels with Bernoulli laws of success probability `θ v x` in `[0, 1]` at the
masked parent configuration `x`. -/
noncomputable def detKernels : G.MarkovKernels (fun _ => Bool) where
  kernel v z b := (bernQ (θ v (extendP G v z)) b : ℝ)
  nonneg v z b := Rat.cast_nonneg.2 (bernQ_nonneg (hθ v _).1 (hθ v _).2 b)
  sum_eq_one v z := by
    simp only [Fintype.sum_bool, bernQ, ↓reduceIte, Bool.false_eq_true]
    push_cast
    ring

/-- The response-function structural causal model realizing `QModel.detKernels`. -/
noncomputable def detModel (hG : G.IsAcyclic) :
    SCM G (fun _ => Bool) (fun v => (G.parentsFinset v → Bool) → Bool) :=
  (detKernels G θ hθ).toSCM hG

variable (hG : G.IsAcyclic)

/-- The factor of `v` in the model is the rational Bernoulli mass at the masked configuration. -/
theorem factor_detModel (v : Fin n) (x : Fin n → Bool) :
    (detModel G θ hθ hG).kernels.factor v x = (bernQ (θ v (maskP G v x)) (x v) : ℝ) := by
  change (Digraph.MarkovKernels.toSCM (detKernels G θ hθ) hG).kernel v _ (x v) = _
  rw [Digraph.MarkovKernels.kernel_toSCM]
  change (bernQ (θ v (extendP G v _)) (x v) : ℝ) = _
  rw [extendP_restrict]

/-- The joint law of the model is the cast of the rational joint mass. -/
theorem dist_detModel (x : Fin n → Bool) : (detModel G θ hθ hG).dist x = (qjoint G θ x : ℝ) := by
  rw [SCM.dist_eq_prod]
  simp only [factor_detModel, qjoint]
  push_cast
  rfl

/-- The marginal masses of the model are the casts of the rational ones. -/
theorem margAt_detModel (S : Finset (Fin n)) (w : Fin n → Bool) :
    (detModel G θ hθ hG).dist.margAt S w = (qmarg G θ S w : ℝ) := by
  unfold qmarg FiniteDist.margAt FiniteDist.prob
  push_cast
  exact sum_congr rfl fun x _ => dist_detModel G θ hθ hG x

/-- The causal effects of the model are the casts of the rational ones, computed by the
truncated factorization. -/
theorem effect_detModel (X : Finset (Fin n)) (xv : Fin n → Bool) (Y : Finset (Fin n))
    (yv : Fin n → Bool) :
    (detModel G θ hθ hG).effect X xv Y yv = (qeffect G θ X xv Y yv : ℝ) := by
  unfold SCM.effect qeffect FiniteDist.margAt FiniteDist.prob
  push_cast
  refine sum_congr rfl fun y _ => ?_
  rw [SCM.dist_intervene, qint]
  split_ifs
  · push_cast
    exact prod_congr rfl fun v _ => factor_detModel G θ hθ hG v y
  · simp

variable {G}

include hG in
/-- **Certificate for non-identifiability, with deterministic kernels allowed.** Two Boolean
models with rational success probabilities in `[0, 1]` on the same acyclic DAG `G`, with
strictly positive and equal rational marginal masses on `O` and different rational effects,
show that the effect `P(Y = y_Y | do(X := x_X))` is not identifiable from the observed law
within the class of models on `G` whose observed law is strictly positive. -/
theorem not_identifiableFrom_of_qmarg_eq_of_pos {θ₁ θ₂ : Fin n → (Fin n → Bool) → ℚ}
    (hθ₁ : ∀ v x, 0 ≤ θ₁ v x ∧ θ₁ v x ≤ 1) (hθ₂ : ∀ v x, 0 ≤ θ₂ v x ∧ θ₂ v x ≤ 1)
    {O : Finset (Fin n)} (hpos : ∀ w, 0 < qmarg G θ₁ O w)
    (hobs : ∀ w, qmarg G θ₁ O w = qmarg G θ₂ O w)
    {X Y : Finset (Fin n)} {x y : Fin n → Bool}
    (hne : qeffect G θ₁ X x Y y ≠ qeffect G θ₂ X x Y y) :
    ¬ SCM.IdentifiableFrom {m : SCM.Model G (fun _ => Bool) | ∀ w, 0 < m.scm.dist.margAt O w} O
      (fun m => m.scm.effect X x Y y) := by
  intro h
  have h₁ : ∀ w, 0 < (detModel G θ₁ hθ₁ hG).dist.margAt O w := fun w => by
    rw [margAt_detModel]
    exact_mod_cast hpos w
  have h₂ : ∀ w, 0 < (detModel G θ₂ hθ₂ hG).dist.margAt O w := fun w => by
    rw [margAt_detModel, ← hobs]
    exact_mod_cast hpos w
  have := h ⟨_, detModel G θ₁ hθ₁ hG⟩ h₁ ⟨_, detModel G θ₂ hθ₂ hG⟩ h₂
    (FiniteDist.marginal_eq_of_margAt_eq fun w => by
      rw [margAt_detModel, margAt_detModel, hobs])
  simp only [effect_detModel] at this
  exact hne (by exact_mod_cast this)

end QModel

namespace IDCompletenessExamples

open QModel IDExamples

/-! ### The three-vertex witness `W → X → Y`, `W ↔ Y`, `X ↔ W` -/

/-- A DAG on `Fin 5` for the witness, with one latent root per bidirected edge (a relabeling of
the canonical construction, with one latent per edge instead of the two of
`ADMG.canonicalDAG`): `W = 0`, `X = 1`, `Y = 2`, the latent `a = 3` of `W ↔ Y` and the latent
`b = 4` of `X ↔ W`, with the edges `W → X`, `X → Y`, `a → W`, `a → Y`, `b → W` and `b → X`. -/
def witDAG : Digraph (Fin 5) := edges [(0, 1), (1, 2), (3, 0), (3, 2), (4, 0), (4, 1)]

instance : DecidableRel witDAG.Adj := inferInstanceAs (DecidableRel (edges _).Adj)

/-- The canonical DAG of the witness is acyclic. -/
theorem witDAG_isAcyclic : witDAG.IsAcyclic :=
  Digraph.isAcyclic_of_adj_lt (fun v : Fin 5 => ![1, 2, 3, 0, 0] v) fun u v h => by
    revert u v h
    decide

/-- The witness ADMG on `Fin 5`: `W → X → Y`, `W ↔ Y` and `X ↔ W`; the latent vertices are
isolated. -/
def witH : ADMG (Fin 5) := mixed [(0, 1), (1, 2)] [(0, 2), (1, 0)]

instance : DecidableRel witH.directed.Adj :=
  inferInstanceAs (DecidableRel (mixed _ _).directed.Adj)
instance : DecidableRel witH.bidirected.Adj :=
  inferInstanceAs (DecidableRel (mixed _ _).bidirected.Adj)

/-- The observed vertices `W`, `X` and `Y`. -/
abbrev witO : Finset (Fin 5) := {0, 1, 2}

/-- The latent projection of the canonical DAG onto `{W, X, Y}` is the witness ADMG. -/
theorem wit_projection : latentProjection witDAG (↑witO)ᶜ = witH := by
  have hroot : ∀ l ∉ witO, ∀ u, ¬ witDAG.Adj u l := by decide
  ext u v
  · rw [latentProjection_directed_adj_of_roots hroot]
    revert u v
    decide
  · rw [latentProjection_bidirected_adj_of_roots hroot]
    revert u v
    decide

/-- **The algorithm fails on the witness graph.** The ancestors of `Y` outside `X` are `{Y}`,
whose district inside the observed vertices is `{W, X, Y}`, and the ancestral closure of `Y`
inside it is the whole district. -/
theorem wit_idAlg : idAlg witH ordFin witO {1} {2} = none := by
  refine idAlg_eq_none witH ordFin (d := {2}) (by decide) ?_
  rw [idPart, show closeIn witH witO {2} = {0, 1, 2} by decide]
  exact identify_of_not _ _ _ (by decide) (by decide)

/-- Model one: fair latent bits `a = 3` and `b = 4`, `W = a + b` and `X = W + b` (sums modulo
two), and `Y = a + n` with `P(n = 1) = 1/4`. -/
def θ₁ (v : Fin 5) (x : Fin 5 → Bool) : ℚ :=
  if v = 0 then (if xor (x 3) (x 4) then 1 else 0)
  else if v = 1 then (if xor (x 0) (x 4) then 1 else 0)
  else if v = 2 then (if x 3 then 3 / 4 else 1 / 4)
  else 1 / 2

/-- Model two: the same `W`, `X` and latent bits, and `Y = X + n` with `P(n = 1) = 1/4`. -/
def θ₂ (v : Fin 5) (x : Fin 5 → Bool) : ℚ :=
  if v = 0 then (if xor (x 3) (x 4) then 1 else 0)
  else if v = 1 then (if xor (x 0) (x 4) then 1 else 0)
  else if v = 2 then (if x 1 then 3 / 4 else 1 / 4)
  else 1 / 2

/-- The success probabilities of model one lie in `[0, 1]`. -/
theorem θ₁_mem (v : Fin 5) (x : Fin 5 → Bool) : 0 ≤ θ₁ v x ∧ θ₁ v x ≤ 1 := by
  unfold θ₁
  split_ifs <;> norm_num

/-- The success probabilities of model two lie in `[0, 1]`. -/
theorem θ₂_mem (v : Fin 5) (x : Fin 5 → Bool) : 0 ≤ θ₂ v x ∧ θ₂ v x ≤ 1 := by
  unfold θ₂
  split_ifs <;> norm_num

/-- The all-true configuration. -/
def allTrue : Fin 5 → Bool := fun _ => true

/-- **Non-identifiability on the witness graph.** Within the class of models on the canonical
DAG whose observed law on `{W, X, Y}` is strictly positive, `P(Y = true | do(X := true))` is
not identifiable: the two models have the same strictly positive observed law and the effects
`1/2` and `3/4`. -/
theorem wit_not_identifiableFrom :
    ¬ SCM.IdentifiableFrom
      {m : SCM.Model witDAG (fun _ => Bool) | ∀ w, 0 < m.scm.dist.margAt witO w} witO
      (fun m => m.scm.effect {1} allTrue {2} allTrue) :=
  not_identifiableFrom_of_qmarg_eq_of_pos witDAG_isAcyclic θ₁_mem θ₂_mem
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The c-factor `Q[{Y}]` on the witness graph is not identifiable.** Within the same class,
`Q[{Y}](w) = P(Y = true | do(W := true, X := true))` is not identifiable: the two models give
`1/2` and `3/4`. -/
theorem wit_cFactor_not_identifiableFrom :
    ¬ SCM.IdentifiableFrom
      {m : SCM.Model witDAG (fun _ => Bool) | ∀ w, 0 < m.scm.dist.margAt witO w} witO
      (fun m => m.scm.cFactor witO {2} allTrue) :=
  not_identifiableFrom_of_qmarg_eq_of_pos (X := witO \ {2}) (Y := {2}) witDAG_isAcyclic θ₁_mem
    θ₂_mem (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The algorithm decides identifiability on the witness graph.** The effect is identifiable
at every configuration, within the class of models on the canonical DAG with a strictly
positive observed law, if and only if the algorithm succeeds on the latent projection
`witH` (`IDCompletenessExamples.wit_projection`). Both sides are false. -/
theorem wit_iff :
    (∀ w, SCM.IdentifiableFrom
      {m : SCM.Model witDAG (fun _ => Bool) | ∀ w, 0 < m.scm.dist.margAt witO w} witO
      (fun m => m.scm.effect {1} w {2} w)) ↔ (idAlg witH ordFin witO {1} {2}).isSome := by
  rw [wit_idAlg]
  exact ⟨fun h => absurd (h allTrue) wit_not_identifiableFrom, fun h => absurd h (by simp)⟩

/-! ### The bow graph -/

/-- **The algorithm decides identifiability on the bow graph.** For the bow DAG of
`SCM.BowExample` (which is the canonical DAG of `X → Y`, `X ↔ Y`), the effect of `X` on `Y` is
identifiable at every configuration, within the class of models with a strictly positive
observed law, if and only if the algorithm succeeds on the latent projection `bowH`. Both sides
are false (`IDExamples.bow_link`). -/
theorem bow_iff :
    (∀ w, SCM.IdentifiableFrom
      {m : SCM.Model SCM.BowExample.bow (fun _ => Bool) |
        ∀ w, 0 < m.scm.dist.margAt {1, 2} w} {1, 2}
      (fun m => m.scm.effect {1} w {2} w)) ↔ (idAlg bowH ordFin {1, 2} {1} {2}).isSome := by
  rw [bow_idAlg]
  exact ⟨fun h => absurd (h SCM.BowExample.treat) bow_link.2.2, fun h => absurd h (by simp)⟩

end IDCompletenessExamples

end CausalInference
