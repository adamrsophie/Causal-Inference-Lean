/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Identification.IDFigure38
public import CausalInference.Identification.QModels

/-!
# Concrete models for the identification examples

Explicit Boolean models with rational kernels (`QModel.model`) on the three example DAGs of
`IDExamples` and `IDFigure38`. Each model has a strictly positive observed law, so the
corresponding soundness corollary applies to it and is not vacuous. For each model the true
effect `P(Y = true | do(X = true))` is computed from the definition of the effect (the
truncated factorization, summing over the latent values), and the identifying formula is
computed from the observed marginals alone; both are the same exact rational, and the two
computations are independent of the soundness theorem. The naive conditional `P(Y = true |
X = true)` is a different rational, so the latent vertices confound.

## Main results

* Figure 3.8(f): `IDConcrete.m38_effect` (`251/400`), `IDConcrete.m38_formula` (`251/400`),
  `IDConcrete.m38_naive` (`1279/2000`), `IDConcrete.m38_adjustment_ne` (no adjustment over a set
  of observed vertices other than `X` and `Y` gives the effect), and
  `IDConcrete.m38_effect_eq_formula`, the soundness corollary instantiated.
* Front door: `IDConcrete.mfd_effect` (`2/5`), `IDConcrete.mfd_formula` (`2/5`),
  `IDConcrete.mfd_naive` (`49/100`), and `IDConcrete.frontDoor_effect_eq`, the soundness
  corollary for every positive model on the front-door DAG.
* Back door: `IDConcrete.mbd_effect` (`2/5`), `IDConcrete.mbd_formula` (`2/5`),
  `IDConcrete.mbd_naive` (`12/25`), and `IDConcrete.backDoor_effect_eq`.
-/

@[expose] public section

namespace CausalInference

namespace IDConcrete

open Finset QModel IDExamples IDFigure38

/-- The all-true configuration. -/
def tt {n : ℕ} : Fin n → Bool := fun _ => true

/-! ### Figure 3.8(f) -/

/-- The success probabilities of the Figure 3.8(f) model. The latent `U = 4` (a parent of `X` and
`Z₂`) and `W = 5` (a parent of `Z₁` and `Y`) are fair bits; `P(X = 1 | u) = 4/5` or `1/5`;
`P(Z₁ = 1 | x, w)` and `P(Z₂ = 1 | z₁, u)` are given by tables; and
`P(Y = 1 | x, z₁, z₂, w) = (1 + 2x + 2z₁ + z₂ + 3w) / 10`. -/
def θ38 (v : Fin 6) (x : Fin 6 → Bool) : ℚ :=
  if v = 0 then (if x 4 then 4 / 5 else 1 / 5)
  else if v = 1 then
    (if x 0 then (if x 5 then 3 / 4 else 1 / 2) else (if x 5 then 1 / 2 else 1 / 4))
  else if v = 2 then
    (if x 1 then (if x 4 then 4 / 5 else 2 / 5) else (if x 4 then 3 / 5 else 1 / 5))
  else if v = 3 then (1 + (if x 0 then 2 else 0) + (if x 1 then 2 else 0) + (if x 2 then 1 else 0)
    + (if x 5 then 3 else 0)) / 10
  else 1 / 2

/-- Every success probability of the model lies strictly between `0` and `1`. -/
theorem θ38_valid : ∀ v x, 0 < θ38 v x ∧ θ38 v x < 1 := by decide +kernel

/-- The DAG of Figure 3.8(f) is acyclic. -/
theorem fig38DAG_isAcyclic : fig38DAG.IsAcyclic := by decide

/-- The concrete model on the DAG of Figure 3.8(f). -/
noncomputable def m38 := model fig38DAG θ38 θ38_valid fig38DAG_isAcyclic

/-- The observed law of the model is strictly positive. -/
theorem m38_pos (w : Fin 6 → Bool) : 0 < m38.dist.margAt obs w :=
  margAt_model_pos _ _ _ _ _ _

/-- Formula (3.48) as a functional of a family of marginal masses `m`. -/
def formula38 {R : Type*} [Field R] (m : Finset (Fin 6) → (Fin 6 → Bool) → R)
    (w : Fin 6 → Bool) : R :=
  ∑ c ∈ FiniteDist.agreeOn ({1, 2} : Finset (Fin 6))ᶜ w,
    m {0, 1, 2, 3} c / m {0, 1, 2} c * (m {0, 1} c / m {0} c) *
      ∑ d ∈ FiniteDist.agreeOn ({0} : Finset (Fin 6))ᶜ c, m {0, 1, 2} d / m {0, 1} d * m {0} d

/-- The formula commutes with the cast from `ℚ` to `ℝ`. -/
theorem formula38_cast (m : Finset (Fin 6) → (Fin 6 → Bool) → ℚ) (w : Fin 6 → Bool) :
    formula38 (fun S c => (m S c : ℝ)) w = ((formula38 m w : ℚ) : ℝ) := by
  unfold formula38
  push_cast
  rfl

/-- The adjustment formula `∑_z P(y | x, z) P(z)` over `Z`, for `X = 0` and `Y = 3`. -/
def adjust38 {R : Type*} [Field R] (m : Finset (Fin 6) → (Fin 6 → Bool) → R) (Z : Finset (Fin 6))
    (w : Fin 6 → Bool) : R :=
  ∑ c ∈ FiniteDist.agreeOn Zᶜ w, m ({3, 0} ∪ Z) c / m ({0} ∪ Z) c * m Z c

/-- The adjustment formula commutes with the cast from `ℚ` to `ℝ`. -/
theorem adjust38_cast (m : Finset (Fin 6) → (Fin 6 → Bool) → ℚ) (Z : Finset (Fin 6))
    (w : Fin 6 → Bool) :
    adjust38 (fun S c => (m S c : ℝ)) Z w = ((adjust38 m Z w : ℚ) : ℝ) := by
  unfold adjust38
  push_cast
  rfl

/-- The marginal masses of the model are casts of rational sums. -/
theorem m38_margAt : m38.dist.margAt = fun S w => (qmarg fig38DAG θ38 S w : ℝ) := by
  funext S w
  exact margAt_model _ _ _ _ S w

/-- **The true effect**, from the truncated factorization: `P(Y = 1 | do(X = 1)) = 251/400`. -/
theorem m38_effect : m38.effect {0} tt {3} tt = 251 / 400 := by
  rw [m38, effect_model]
  have h : qeffect fig38DAG θ38 {0} tt {3} tt = 251 / 400 := by decide +kernel
  rw [h]
  norm_num

/-- **Formula (3.48) from the observed marginals alone** evaluates to `251/400`. -/
theorem m38_formula : formula38 m38.dist.margAt tt = 251 / 400 := by
  have h : formula38 (qmarg fig38DAG θ38) tt = 251 / 400 := by decide +kernel
  rw [m38_margAt, formula38_cast, h]
  norm_num

/-- **The naive conditional differs**: `P(Y = 1 | X = 1) = 1279/2000`. -/
theorem m38_naive : m38.dist.margAt {0, 3} tt / m38.dist.margAt {0} tt = 1279 / 2000 := by
  have h : qmarg fig38DAG θ38 {0, 3} tt / qmarg fig38DAG θ38 {0} tt = 1279 / 2000 := by
    decide +kernel
  rw [m38_margAt]
  beta_reduce
  rw [← Rat.cast_div, h]
  norm_num

/-- **No adjustment over observed vertices gives the effect**: for every `Z ⊆ {Z₁, Z₂}`, the
adjustment formula differs from `251/400` (its values are `1279/2000`, `301/500`, `7531/12212`
and `59/100`). -/
theorem m38_adjustment_ne : ∀ Z ∈ ({1, 2} : Finset (Fin 6)).powerset,
    adjust38 m38.dist.margAt Z tt ≠ m38.effect {0} tt {3} tt := by
  have h : ∀ Z ∈ ({1, 2} : Finset (Fin 6)).powerset,
      adjust38 (qmarg fig38DAG θ38) Z tt ≠ 251 / 400 := by decide +kernel
  intro Z hZ heq
  rw [m38_effect, m38_margAt, adjust38_cast] at heq
  exact h Z hZ (Rat.cast_injective (α := ℝ) (heq.trans (by norm_num)))

/-- The soundness corollary `IDFigure38.effect_eq_formula` applies to the concrete model. -/
theorem m38_effect_eq_formula :
    m38.effect {0} tt {3} tt = formula38 m38.dist.margAt tt :=
  effect_eq_formula m38 m38_pos tt

/-! ### The front-door graph -/

/-- The success probabilities of the front-door model: `U = 3` a fair bit,
`P(X = 1 | u) = 4/5` or `1/5`, `P(Z = 1 | x) = 3/4` or `1/4`, and
`P(Y = 1 | z, u) = (1 + 2z + 3u) / 10`. -/
def θfd (v : Fin 4) (x : Fin 4 → Bool) : ℚ :=
  if v = 0 then (if x 3 then 4 / 5 else 1 / 5)
  else if v = 1 then (if x 0 then 3 / 4 else 1 / 4)
  else if v = 2 then (1 + (if x 1 then 2 else 0) + (if x 3 then 3 else 0)) / 10
  else 1 / 2

/-- Every success probability of the model lies strictly between `0` and `1`. -/
theorem θfd_valid : ∀ v x, 0 < θfd v x ∧ θfd v x < 1 := by decide +kernel

/-- The front-door DAG is acyclic. -/
theorem fdDAG_isAcyclic : fdDAG.IsAcyclic := by decide

/-- The front-door formula as a functional of a family of marginal masses `m`. -/
def formulaFD {R : Type*} [Field R] (m : Finset (Fin 4) → (Fin 4 → Bool) → R)
    (w : Fin 4 → Bool) : R :=
  ∑ c ∈ FiniteDist.agreeOn ({1} : Finset (Fin 4))ᶜ w, m ({1} ∪ {0}) c / m {0} c *
    ∑ d ∈ FiniteDist.agreeOn ({0} : Finset (Fin 4))ᶜ c,
      m ({2} ∪ {1} ∪ {0}) d / m ({1} ∪ {0}) d * m {0} d

/-- The formula commutes with the cast from `ℚ` to `ℝ`. -/
theorem formulaFD_cast (m : Finset (Fin 4) → (Fin 4 → Bool) → ℚ) (w : Fin 4 → Bool) :
    formulaFD (fun S c => (m S c : ℝ)) w = ((formulaFD m w : ℚ) : ℝ) := by
  unfold formulaFD
  push_cast
  rfl

/-- **Soundness on the front-door graph**: for every model on the front-door DAG with a strictly
positive observed law, `P(Y = w_Y | do(X := w_X))` is the front-door formula. -/
theorem frontDoor_effect_eq {α : Fin 4 → Type} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    {ε : Fin 4 → Type*} [∀ v, Fintype (ε v)] (M : SCM fdDAG α ε)
    (hpos : ∀ w, 0 < M.dist.margAt {0, 1, 2} w) (w : ∀ v, α v) :
    M.effect {0} w {2} w = ∑ c ∈ FiniteDist.agreeOn ({1} : Finset (Fin 4))ᶜ w,
      M.dist.margAt ({1} ∪ {0}) c / M.dist.margAt {0} c *
        ∑ d ∈ FiniteDist.agreeOn ({0} : Finset (Fin 4))ᶜ c,
          M.dist.margAt ({2} ∪ {1} ∪ {0}) d / M.dist.margAt ({1} ∪ {0}) d *
            M.dist.margAt {0} d := by
  obtain ⟨e, he, heval⟩ := frontDoor_idAlg
  rw [M.effect_eq_eval_of_idAlg fdDAG_projection ordFin ordFin_injective.injOn fdH_ord hpos
    he w, heval]

/-- The concrete front-door model. -/
noncomputable def mfd := model fdDAG θfd θfd_valid fdDAG_isAcyclic

/-- The observed law of the front-door model is strictly positive. -/
theorem mfd_pos (w : Fin 4 → Bool) : 0 < mfd.dist.margAt {0, 1, 2} w :=
  margAt_model_pos _ _ _ _ _ _

/-- The marginal masses of the model are casts of rational sums. -/
theorem mfd_margAt : mfd.dist.margAt = fun S w => (qmarg fdDAG θfd S w : ℝ) := by
  funext S w
  exact margAt_model _ _ _ _ S w

/-- The true front-door effect: `P(Y = 1 | do(X = 1)) = 2/5`. -/
theorem mfd_effect : mfd.effect {0} tt {2} tt = 2 / 5 := by
  rw [mfd, effect_model]
  have h : qeffect fdDAG θfd {0} tt {2} tt = 2 / 5 := by decide +kernel
  rw [h]
  norm_num

/-- The front-door formula from the observed marginals alone: `2/5`. -/
theorem mfd_formula : formulaFD mfd.dist.margAt tt = 2 / 5 := by
  have h : formulaFD (qmarg fdDAG θfd) tt = 2 / 5 := by decide +kernel
  rw [mfd_margAt, formulaFD_cast, h]
  norm_num

/-- The naive conditional on the front-door model: `P(Y = 1 | X = 1) = 49/100`. -/
theorem mfd_naive : mfd.dist.margAt {0, 2} tt / mfd.dist.margAt {0} tt = 49 / 100 := by
  have h : qmarg fdDAG θfd {0, 2} tt / qmarg fdDAG θfd {0} tt = 49 / 100 := by decide +kernel
  rw [mfd_margAt]
  beta_reduce
  rw [← Rat.cast_div, h]
  norm_num

/-- The soundness corollary applies to the concrete front-door model. -/
theorem mfd_effect_eq_formula : mfd.effect {0} tt {2} tt = formulaFD mfd.dist.margAt tt :=
  frontDoor_effect_eq mfd mfd_pos tt

/-! ### The back-door graph -/

/-- The success probabilities of the back-door model: `P(Z = 1) = 1/3`,
`P(X = 1 | z) = 3/4` or `1/4`, and `P(Y = 1 | x, z) = (1 + 2x + 3z) / 10`. -/
def θbd (v : Fin 3) (x : Fin 3 → Bool) : ℚ :=
  if v = 0 then 1 / 3
  else if v = 1 then (if x 0 then 3 / 4 else 1 / 4)
  else (1 + (if x 1 then 2 else 0) + (if x 0 then 3 else 0)) / 10

/-- Every success probability of the model lies strictly between `0` and `1`. -/
theorem θbd_valid : ∀ v x, 0 < θbd v x ∧ θbd v x < 1 := by decide +kernel

/-- The back-door DAG is acyclic. -/
theorem bdDAG_isAcyclic : bdDAG.IsAcyclic := by decide

/-- The adjustment formula as a functional of a family of marginal masses `m`. -/
def formulaBD {R : Type*} [Field R] (m : Finset (Fin 3) → (Fin 3 → Bool) → R)
    (w : Fin 3 → Bool) : R :=
  ∑ c ∈ FiniteDist.agreeOn ({0} : Finset (Fin 3))ᶜ w,
    m ({2} ∪ {1} ∪ {0}) c / m ({1} ∪ {0}) c * m {0} c

/-- The formula commutes with the cast from `ℚ` to `ℝ`. -/
theorem formulaBD_cast (m : Finset (Fin 3) → (Fin 3 → Bool) → ℚ) (w : Fin 3 → Bool) :
    formulaBD (fun S c => (m S c : ℝ)) w = ((formulaBD m w : ℚ) : ℝ) := by
  unfold formulaBD
  push_cast
  rfl

/-- **Soundness on the back-door graph**: for every model on the back-door DAG with a strictly
positive joint law, `P(Y = w_Y | do(X := w_X))` is the adjustment formula. -/
theorem backDoor_effect_eq {α : Fin 3 → Type} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    {ε : Fin 3 → Type*} [∀ v, Fintype (ε v)] (M : SCM bdDAG α ε)
    (hpos : ∀ w, 0 < M.dist.margAt {0, 1, 2} w) (w : ∀ v, α v) :
    M.effect {1} w {2} w = ∑ c ∈ FiniteDist.agreeOn ({0} : Finset (Fin 3))ᶜ w,
      M.dist.margAt ({2} ∪ {1} ∪ {0}) c / M.dist.margAt ({1} ∪ {0}) c * M.dist.margAt {0} c := by
  obtain ⟨e, he, heval⟩ := backDoor_idAlg
  rw [M.effect_eq_eval_of_idAlg bdDAG_projection ordFin ordFin_injective.injOn bdH_ord hpos
    he w, heval]

/-- The concrete back-door model. -/
noncomputable def mbd := model bdDAG θbd θbd_valid bdDAG_isAcyclic

/-- The joint law of the back-door model is strictly positive. -/
theorem mbd_pos (w : Fin 3 → Bool) : 0 < mbd.dist.margAt {0, 1, 2} w :=
  margAt_model_pos _ _ _ _ _ _

/-- The marginal masses of the model are casts of rational sums. -/
theorem mbd_margAt : mbd.dist.margAt = fun S w => (qmarg bdDAG θbd S w : ℝ) := by
  funext S w
  exact margAt_model _ _ _ _ S w

/-- The true back-door effect: `P(Y = 1 | do(X = 1)) = 2/5`. -/
theorem mbd_effect : mbd.effect {1} tt {2} tt = 2 / 5 := by
  rw [mbd, effect_model]
  have h : qeffect bdDAG θbd {1} tt {2} tt = 2 / 5 := by decide +kernel
  rw [h]
  norm_num

/-- The adjustment formula from the observed law: `2/5`. -/
theorem mbd_formula : formulaBD mbd.dist.margAt tt = 2 / 5 := by
  have h : formulaBD (qmarg bdDAG θbd) tt = 2 / 5 := by decide +kernel
  rw [mbd_margAt, formulaBD_cast, h]
  norm_num

/-- The naive conditional on the back-door model: `P(Y = 1 | X = 1) = 12/25`. -/
theorem mbd_naive : mbd.dist.margAt {1, 2} tt / mbd.dist.margAt {1} tt = 12 / 25 := by
  have h : qmarg bdDAG θbd {1, 2} tt / qmarg bdDAG θbd {1} tt = 12 / 25 := by decide +kernel
  rw [mbd_margAt]
  beta_reduce
  rw [← Rat.cast_div, h]
  norm_num

/-- The soundness corollary applies to the concrete back-door model. -/
theorem mbd_effect_eq_formula : mbd.effect {1} tt {2} tt = formulaBD mbd.dist.margAt tt :=
  backDoor_effect_eq mbd mbd_pos tt

end IDConcrete

end CausalInference
