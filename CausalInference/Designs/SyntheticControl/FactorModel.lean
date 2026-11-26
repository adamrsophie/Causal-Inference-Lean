/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.SyntheticControl.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Synthetic control under a noiseless linear factor model

Abadie, Diamond and Hainmueller (2010), "Synthetic control methods for comparative case
studies", justify synthetic control weights under the linear factor model
`Y_i(0) t = δ t + θ t ⬝ Z_i + λ t ⬝ μ_i + ε_i t`, with observed covariates `Z_i`, unobserved
factor loadings `μ_i`, common factors `λ t`, and noise `ε`. We formalize the noiseless version
(`ε = 0`), which isolates the algebra of their argument; no statement here concerns noise, bias
bounds, or inference.

## Main definitions

* `SyntheticControl.factorOutcome δ θ lam Z μ t`: the noiseless factor model outcome
  `δ t + θ t ⬝ᵥ Z + lam t ⬝ᵥ μ`.
* `SyntheticControl.factorGram lam`: the matrix `∑ t, lam tᵀ lam t` of a finite family of factor
  vectors, as outer products.

## Main results

* `factorOutcome_sub_synth`: for weights summing to one, the counterfactual mismatch equals
  `θ t ⬝ᵥ (Z₁ - ∑ w j Z j) + lam t ⬝ᵥ (μ₁ - ∑ w j μ j)`.
* `factorOutcome_sub_synth_eq_zero`: matching covariates and loadings gives zero bias.
* `loadings_eq_of_preFit`: if the pre-treatment factor matrix is invertible, exact
  pre-treatment fit together with covariate fit forces the loadings to match.
* `factorOutcome_sub_synth_eq_zero_of_preFit`: hence the post-treatment bias is zero.
* `rank_condition_counterexample`: when the rank condition fails (a
  factor inactive before treatment), exact pre-treatment fit can coexist with a nonzero bias.
-/

@[expose] public section

open Matrix

namespace CausalInference

namespace SyntheticControl

variable {J R F T : Type*} [Fintype J] [Fintype R] [Fintype F]

/-- The noiseless linear factor model outcome of a unit with covariates `Z` and factor loadings
`μ` at time `t`: `δ t + θ t ⬝ᵥ Z + lam t ⬝ᵥ μ`. -/
def factorOutcome (δ : T → ℝ) (θ : T → R → ℝ) (lam : T → F → ℝ) (Z : R → ℝ) (μ : F → ℝ)
    (t : T) : ℝ :=
  δ t + θ t ⬝ᵥ Z + lam t ⬝ᵥ μ

/-- The synthetic control of donors following the factor model is the factor model outcome
evaluated at the weighted covariates and loadings, with the time effect scaled by the total
weight. -/
theorem synth_factorOutcome (δ : T → ℝ) (θ : T → R → ℝ) (lam : T → F → ℝ) (Z : J → R → ℝ)
    (μ : J → F → ℝ) (w : J → ℝ) (t : T) :
    synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t
      = (∑ j, w j) * δ t + θ t ⬝ᵥ (∑ j, w j • Z j) + lam t ⬝ᵥ (∑ j, w j • μ j) := by
  simp only [synth, factorOutcome, dotProduct_sum, dotProduct_smul, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul]

/-- **Bias formula in the factor model.** For weights summing to one, the treated unit's
untreated outcome minus its synthetic control is
`θ t ⬝ᵥ (Z₁ - ∑ j, w j • Z j) + lam t ⬝ᵥ (μ₁ - ∑ j, w j • μ j)`. -/
theorem factorOutcome_sub_synth (δ : T → ℝ) (θ : T → R → ℝ) (lam : T → F → ℝ) (Z₁ : R → ℝ)
    (μ₁ : F → ℝ) (Z : J → R → ℝ) (μ : J → F → ℝ) (w : J → ℝ) (hw : ∑ j, w j = 1) (t : T) :
    factorOutcome δ θ lam Z₁ μ₁ t - synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t
      = θ t ⬝ᵥ (Z₁ - ∑ j, w j • Z j) + lam t ⬝ᵥ (μ₁ - ∑ j, w j • μ j) := by
  rw [synth_factorOutcome, hw, factorOutcome, dotProduct_sub, dotProduct_sub]
  ring

/-- **Zero bias from matched covariates and loadings.** In the noiseless factor model, if
weights summing to one reproduce the treated unit's covariates `Z₁` and its unobserved factor
loadings `μ₁`, the synthetic control equals the treated unit's untreated outcome at every time,
so in particular the post-treatment bias is zero. -/
theorem factorOutcome_sub_synth_eq_zero (δ : T → ℝ) (θ : T → R → ℝ) (lam : T → F → ℝ)
    (Z₁ : R → ℝ) (μ₁ : F → ℝ) (Z : J → R → ℝ) (μ : J → F → ℝ) (w : J → ℝ)
    (hw : ∑ j, w j = 1) (hZ : ∑ j, w j • Z j = Z₁) (hμ : ∑ j, w j • μ j = μ₁) (t : T) :
    factorOutcome δ θ lam Z₁ μ₁ t - synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t
      = 0 := by
  rw [factorOutcome_sub_synth δ θ lam Z₁ μ₁ Z μ w hw, hZ, hμ]
  simp

/-! ### Matching on pre-treatment outcomes suffices under a rank condition -/

/-- The factor matrix `∑_{t ∈ pre} lam tᵀ lam t` of the periods in `pre`, a sum of outer
products. It is invertible exactly when the factor vectors of those periods span `F → ℝ`. -/
def factorGram (pre : Finset T) (lam : T → F → ℝ) : Matrix F F ℝ :=
  ∑ t ∈ pre, vecMulVec (lam t) (lam t)

/-- Multiplying the factor matrix by a vector `d` gives `∑_{t ∈ pre} (lam t ⬝ᵥ d) • lam t`. -/
theorem factorGram_mulVec (pre : Finset T) (lam : T → F → ℝ) (d : F → ℝ) :
    factorGram pre lam *ᵥ d = ∑ t ∈ pre, (lam t ⬝ᵥ d) • lam t := by
  rw [factorGram, sum_mulVec]
  refine Finset.sum_congr rfl fun t _ => ?_
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

/-- **Loadings are matched by pre-treatment fit (ADH rank argument, noiseless).** In the
noiseless factor model, let the weights sum to one and reproduce the treated unit's covariates.
If the synthetic control fits the treated unit's untreated outcome exactly in every period of
`pre` and the factor matrix `∑_{t ∈ pre} lam tᵀ lam t` is invertible, then the weights also
reproduce the treated unit's unobserved factor loadings. -/
theorem loadings_eq_of_preFit [DecidableEq F] (δ : T → ℝ) (θ : T → R → ℝ) (lam : T → F → ℝ)
    (Z₁ : R → ℝ) (μ₁ : F → ℝ) (Z : J → R → ℝ) (μ : J → F → ℝ) (w : J → ℝ) (pre : Finset T)
    (hw : ∑ j, w j = 1) (hZ : ∑ j, w j • Z j = Z₁)
    (hpre : ∀ t ∈ pre,
      factorOutcome δ θ lam Z₁ μ₁ t = synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t)
    (hrank : IsUnit (factorGram pre lam)) :
    ∑ j, w j • μ j = μ₁ := by
  have horth : ∀ t ∈ pre, lam t ⬝ᵥ (μ₁ - ∑ j, w j • μ j) = 0 := by
    intro t ht
    have h := factorOutcome_sub_synth δ θ lam Z₁ μ₁ Z μ w hw t
    rw [hpre t ht, sub_self, hZ, sub_self, dotProduct_zero, zero_add] at h
    exact h.symm
  have hzero : factorGram pre lam *ᵥ (μ₁ - ∑ j, w j • μ j) = factorGram pre lam *ᵥ 0 := by
    rw [factorGram_mulVec, mulVec_zero]
    exact Finset.sum_eq_zero fun t ht => by rw [horth t ht, zero_smul]
  exact (sub_eq_zero.mp (mulVec_injective_of_isUnit hrank hzero)).symm

/-- **Zero post-treatment bias from pre-treatment fit (ADH, noiseless).** In the noiseless
factor model, if weights summing to one reproduce the treated unit's covariates and fit its
untreated outcome exactly in every period of `pre`, and the pre-treatment factor matrix
`∑_{t ∈ pre} lam tᵀ lam t` is invertible, then the synthetic control equals the treated unit's
untreated outcome at every time `t`, in particular in every post-treatment period. -/
theorem factorOutcome_sub_synth_eq_zero_of_preFit [DecidableEq F] (δ : T → ℝ) (θ : T → R → ℝ)
    (lam : T → F → ℝ) (Z₁ : R → ℝ) (μ₁ : F → ℝ) (Z : J → R → ℝ) (μ : J → F → ℝ) (w : J → ℝ)
    (pre : Finset T) (hw : ∑ j, w j = 1) (hZ : ∑ j, w j • Z j = Z₁)
    (hpre : ∀ t ∈ pre,
      factorOutcome δ θ lam Z₁ μ₁ t = synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t)
    (hrank : IsUnit (factorGram pre lam)) (t : T) :
    factorOutcome δ θ lam Z₁ μ₁ t - synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t
      = 0 :=
  factorOutcome_sub_synth_eq_zero δ θ lam Z₁ μ₁ Z μ w hw hZ
    (loadings_eq_of_preFit δ θ lam Z₁ μ₁ Z μ w pre hw hZ hpre hrank) t

/-! ### Counterexample: the rank condition cannot be dropped

One donor, one covariate, one factor, two periods (`0` pre-treatment, `1` post-treatment).
The factor is inactive before treatment: `lam 0 = 0`, `lam 1 = 1`. The treated unit has loading
`1` and the donor loading `0`; time effects, covariate coefficients and covariates are zero.
The weight `1` on the single donor fits the covariates and the pre-treatment outcome exactly,
yet the post-treatment bias is `1`, because the pre-treatment factor matrix is zero. -/

/-- The factor path of the counterexample: zero before treatment, one after. -/
def cexLam (t : Fin 2) (_ : Unit) : ℝ :=
  if t = 1 then 1 else 0

/-- **Counterexample to matching on pre-treatment outcomes without the rank condition.** With
the single donor weighted by `1` (a point of the simplex), covariates are matched and the
pre-treatment fit is exact, but the pre-treatment factor matrix is not invertible and the
post-treatment bias is `1`, not `0`. -/
theorem rank_condition_counterexample :
    let δ : Fin 2 → ℝ := fun _ => 0
    let θ : Fin 2 → Unit → ℝ := fun _ _ => 0
    let Z₁ : Unit → ℝ := fun _ => 0
    let μ₁ : Unit → ℝ := fun _ => 1
    let Z : Unit → Unit → ℝ := fun _ _ => 0
    let μ : Unit → Unit → ℝ := fun _ _ => 0
    let w : Unit → ℝ := fun _ => 1
    let pre : Finset (Fin 2) := {0}
    (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ ∑ j, w j • Z j = Z₁ ∧
      (∀ t ∈ pre, factorOutcome δ θ cexLam Z₁ μ₁ t
        = synth w (fun j => factorOutcome δ θ cexLam (Z j) (μ j)) t) ∧
      ¬ IsUnit (factorGram pre cexLam) ∧
      factorOutcome δ θ cexLam Z₁ μ₁ 1
        - synth w (fun j => factorOutcome δ θ cexLam (Z j) (μ j)) 1 = 1 := by
  intro δ θ Z₁ μ₁ Z μ w pre
  have hgram : factorGram pre cexLam = 0 := by
    ext i k
    simp [factorGram, pre, cexLam, vecMulVec]
  refine ⟨fun _ => zero_le_one, by simp [w], by ext; simp [w, Z, Z₁], ?_, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton.mp ht]
    simp [factorOutcome, synth, cexLam, δ, θ, Z₁, μ₁, Z, μ, w]
  · rw [hgram]
    exact not_isUnit_zero
  · simp [factorOutcome, synth, cexLam, δ, θ, Z₁, μ₁, Z, μ, w]

end SyntheticControl

end CausalInference
