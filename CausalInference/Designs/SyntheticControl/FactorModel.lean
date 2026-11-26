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
* `SyntheticControl.factorGram pre lam`: the matrix `∑_{t ∈ pre} lam tᵀ lam t` of a finite
  family of factor vectors, as outer products.
* `SyntheticControl.preFactorMatrix pre lam`: the rectangular matrix with rows `lam t`,
  `t ∈ pre`.

## Main results

* `factorOutcome_sub_synth`: for weights summing to one, the counterfactual mismatch equals
  `θ t ⬝ᵥ (Z₁ - ∑ w j Z j) + lam t ⬝ᵥ (μ₁ - ∑ w j μ j)`.
* `factorOutcome_sub_synth_eq_zero`: matching covariates and loadings gives zero bias.
* `isUnit_factorGram_iff`, `injective_preFactorMatrix_mulVec_iff`,
  `isUnit_factorGram_iff_injective`: three equivalent forms of the rank condition (invertible
  Gram matrix; no nonzero vector orthogonal to all pre-treatment factors; full column rank of
  the pre-treatment factor matrix).
* `loadings_eq_of_preFit`: under the rank condition, exact pre-treatment fit together with
  covariate fit forces the loadings to match (`loadings_eq_of_preFit_of_isUnit`: Gram form).
* `factorOutcome_sub_synth_eq_zero_of_preFit`: hence the post-treatment bias is zero.
* `effectHat_eq_effect_of_preFit`: end to end on the panel `Tpre ⊕ Tpost`, zero observed
  pre-treatment loss, covariate balance, unit-sum weights, and the rank condition imply that the
  estimate computed from observed data equals the true effect in every post-treatment period.
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
products. By `isUnit_factorGram_iff` it is invertible exactly when no nonzero vector is
orthogonal to every factor vector of those periods. -/
def factorGram (pre : Finset T) (lam : T → F → ℝ) : Matrix F F ℝ :=
  ∑ t ∈ pre, vecMulVec (lam t) (lam t)

/-- Multiplying the factor matrix by a vector `d` gives `∑_{t ∈ pre} (lam t ⬝ᵥ d) • lam t`. -/
theorem factorGram_mulVec (pre : Finset T) (lam : T → F → ℝ) (d : F → ℝ) :
    factorGram pre lam *ᵥ d = ∑ t ∈ pre, (lam t ⬝ᵥ d) • lam t := by
  rw [factorGram, sum_mulVec]
  refine Finset.sum_congr rfl fun t _ => ?_
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

/-- The quadratic form of the factor matrix is a sum of squares:
`d ⬝ᵥ (G *ᵥ d) = ∑_{t ∈ pre} (lam t ⬝ᵥ d) ^ 2`. -/
theorem dotProduct_factorGram_mulVec (pre : Finset T) (lam : T → F → ℝ) (d : F → ℝ) :
    d ⬝ᵥ (factorGram pre lam *ᵥ d) = ∑ t ∈ pre, (lam t ⬝ᵥ d) ^ 2 := by
  rw [factorGram_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm, sq]

/-- **Rank condition, Gram form.** The pre-treatment factor matrix is invertible if and only if
the only vector orthogonal to every pre-treatment factor vector is zero. -/
theorem isUnit_factorGram_iff [DecidableEq F] (pre : Finset T) (lam : T → F → ℝ) :
    IsUnit (factorGram pre lam) ↔ ∀ d : F → ℝ, (∀ t ∈ pre, lam t ⬝ᵥ d = 0) → d = 0 := by
  constructor
  · intro hG d hd
    refine mulVec_injective_of_isUnit hG ?_
    rw [factorGram_mulVec, mulVec_zero]
    exact Finset.sum_eq_zero fun t ht => by rw [hd t ht, zero_smul]
  · intro h
    rw [← mulVec_injective_iff_isUnit]
    intro a b hab
    rw [← sub_eq_zero]
    refine h _ fun t ht => ?_
    have hzero : factorGram pre lam *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
    have hsq := dotProduct_factorGram_mulVec pre lam (a - b)
    rw [hzero, dotProduct_zero, eq_comm,
      Finset.sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg _] at hsq
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (hsq t ht)

/-- The pre-treatment factor matrix: the rectangular matrix whose rows are the factor vectors
`lam t` of the periods `t ∈ pre`. -/
def preFactorMatrix (pre : Finset T) (lam : T → F → ℝ) : Matrix pre F ℝ :=
  Matrix.of fun t => lam t

/-- **Rank condition, matrix form.** The pre-treatment factor matrix is injective (has full
column rank) if and only if the only vector orthogonal to every pre-treatment factor vector is
zero. -/
theorem injective_preFactorMatrix_mulVec_iff (pre : Finset T) (lam : T → F → ℝ) :
    Function.Injective (preFactorMatrix pre lam).mulVec
      ↔ ∀ d : F → ℝ, (∀ t ∈ pre, lam t ⬝ᵥ d = 0) → d = 0 := by
  have happ : ∀ (d : F → ℝ) (t : pre), (preFactorMatrix pre lam *ᵥ d) t = lam t ⬝ᵥ d :=
    fun d t => rfl
  constructor
  · intro hL d hd
    refine hL ?_
    ext t
    rw [happ, mulVec_zero, hd t t.2]
    rfl
  · intro h a b hab
    rw [← sub_eq_zero]
    refine h _ fun t ht => ?_
    have := congrFun hab ⟨t, ht⟩
    rw [happ, happ] at this
    rw [dotProduct_sub, this, sub_self]

/-- The pre-treatment factor matrix `∑_{t ∈ pre} lam tᵀ lam t` is invertible if and only if the
rectangular pre-treatment factor matrix has full column rank. -/
theorem isUnit_factorGram_iff_injective [DecidableEq F] (pre : Finset T) (lam : T → F → ℝ) :
    IsUnit (factorGram pre lam) ↔ Function.Injective (preFactorMatrix pre lam).mulVec := by
  rw [isUnit_factorGram_iff, injective_preFactorMatrix_mulVec_iff]

/-- **Loadings are matched by pre-treatment fit (ADH rank argument, noiseless).** In the
noiseless factor model, let the weights sum to one and reproduce the treated unit's covariates.
If the synthetic control fits the treated unit's untreated outcome exactly in every period of
`pre` and no nonzero vector is orthogonal to all the factor vectors of those periods (the rank
condition), then the weights also reproduce the treated unit's unobserved factor loadings. -/
theorem loadings_eq_of_preFit (δ : T → ℝ) (θ : T → R → ℝ) (lam : T → F → ℝ)
    (Z₁ : R → ℝ) (μ₁ : F → ℝ) (Z : J → R → ℝ) (μ : J → F → ℝ) (w : J → ℝ) (pre : Finset T)
    (hw : ∑ j, w j = 1) (hZ : ∑ j, w j • Z j = Z₁)
    (hpre : ∀ t ∈ pre,
      factorOutcome δ θ lam Z₁ μ₁ t = synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t)
    (hrank : ∀ d : F → ℝ, (∀ t ∈ pre, lam t ⬝ᵥ d = 0) → d = 0) :
    ∑ j, w j • μ j = μ₁ := by
  have := hrank (μ₁ - ∑ j, w j • μ j) fun t ht => by
    have h := factorOutcome_sub_synth δ θ lam Z₁ μ₁ Z μ w hw t
    rw [hpre t ht, sub_self, hZ, sub_self, dotProduct_zero, zero_add] at h
    exact h.symm
  exact (sub_eq_zero.mp this).symm

/-- The rank argument of `loadings_eq_of_preFit` with the rank condition stated as invertibility
of the pre-treatment factor matrix `∑_{t ∈ pre} lam tᵀ lam t`. -/
theorem loadings_eq_of_preFit_of_isUnit [DecidableEq F] (δ : T → ℝ) (θ : T → R → ℝ)
    (lam : T → F → ℝ) (Z₁ : R → ℝ) (μ₁ : F → ℝ) (Z : J → R → ℝ) (μ : J → F → ℝ) (w : J → ℝ)
    (pre : Finset T) (hw : ∑ j, w j = 1) (hZ : ∑ j, w j • Z j = Z₁)
    (hpre : ∀ t ∈ pre,
      factorOutcome δ θ lam Z₁ μ₁ t = synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t)
    (hrank : IsUnit (factorGram pre lam)) :
    ∑ j, w j • μ j = μ₁ :=
  loadings_eq_of_preFit δ θ lam Z₁ μ₁ Z μ w pre hw hZ hpre
    ((isUnit_factorGram_iff pre lam).mp hrank)

/-- **Zero post-treatment bias from pre-treatment fit (ADH, noiseless).** In the noiseless
factor model, if weights summing to one reproduce the treated unit's covariates and fit its
untreated outcome exactly in every period of `pre`, and no nonzero vector is orthogonal to all
the factor vectors of those periods, then the synthetic control equals the treated unit's
untreated outcome at every time `t`, in particular in every post-treatment period. -/
theorem factorOutcome_sub_synth_eq_zero_of_preFit (δ : T → ℝ) (θ : T → R → ℝ)
    (lam : T → F → ℝ) (Z₁ : R → ℝ) (μ₁ : F → ℝ) (Z : J → R → ℝ) (μ : J → F → ℝ) (w : J → ℝ)
    (pre : Finset T) (hw : ∑ j, w j = 1) (hZ : ∑ j, w j • Z j = Z₁)
    (hpre : ∀ t ∈ pre,
      factorOutcome δ θ lam Z₁ μ₁ t = synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t)
    (hrank : ∀ d : F → ℝ, (∀ t ∈ pre, lam t ⬝ᵥ d = 0) → d = 0) (t : T) :
    factorOutcome δ θ lam Z₁ μ₁ t - synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t
      = 0 :=
  factorOutcome_sub_synth_eq_zero δ θ lam Z₁ μ₁ Z μ w hw hZ
    (loadings_eq_of_preFit δ θ lam Z₁ μ₁ Z μ w pre hw hZ hpre hrank) t

/-- `factorOutcome_sub_synth_eq_zero_of_preFit` with the rank condition stated as invertibility
of the pre-treatment factor matrix `∑_{t ∈ pre} lam tᵀ lam t`. -/
theorem factorOutcome_sub_synth_eq_zero_of_preFit_of_isUnit [DecidableEq F] (δ : T → ℝ)
    (θ : T → R → ℝ) (lam : T → F → ℝ) (Z₁ : R → ℝ) (μ₁ : F → ℝ) (Z : J → R → ℝ)
    (μ : J → F → ℝ) (w : J → ℝ) (pre : Finset T) (hw : ∑ j, w j = 1)
    (hZ : ∑ j, w j • Z j = Z₁)
    (hpre : ∀ t ∈ pre,
      factorOutcome δ θ lam Z₁ μ₁ t = synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t)
    (hrank : IsUnit (factorGram pre lam)) (t : T) :
    factorOutcome δ θ lam Z₁ μ₁ t - synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) t
      = 0 :=
  factorOutcome_sub_synth_eq_zero_of_preFit δ θ lam Z₁ μ₁ Z μ w pre hw hZ hpre
    ((isUnit_factorGram_iff pre lam).mp hrank) t

/-! ### End to end: from observed pre-treatment fit to the post-treatment effect

Time is `Tpre ⊕ Tpost` and the untreated potential outcomes of the treated unit and of the
donors follow the noiseless factor model. Everything is stated on observed data through
`PanelConsistent`. -/

/-- **Exact recovery of the effect from observed pre-treatment fit (ADH, noiseless).** On the
panel `Tpre ⊕ Tpost`, suppose observation consistency holds (`PanelConsistent`), the untreated
potential outcomes of the treated unit and of the donors follow the noiseless factor model,
the weights sum to one and reproduce the treated unit's covariates, the pre-treatment loss on
the observed data is zero, and no nonzero vector is orthogonal to every pre-treatment factor
vector. Then in every post-treatment period the estimated effect computed from observed data
equals the true effect `Y1₁ t - Y0₁ (inr t)`. Weights need not be nonnegative. -/
theorem effectHat_eq_effect_of_preFit {Tpre Tpost : Type*} [Fintype Tpre]
    (δ : Tpre ⊕ Tpost → ℝ) (θ : Tpre ⊕ Tpost → R → ℝ) (lam : Tpre ⊕ Tpost → F → ℝ)
    (Z₁ : R → ℝ) (μ₁ : F → ℝ) (Z : J → R → ℝ) (μ : J → F → ℝ)
    (Yobs₁ : Tpre ⊕ Tpost → ℝ) (Yobs : J → Tpre ⊕ Tpost → ℝ) (Y1₁ : Tpost → ℝ)
    (Y0₁ : Tpre ⊕ Tpost → ℝ) (Y0 : J → Tpre ⊕ Tpost → ℝ)
    (hcons : PanelConsistent Yobs₁ Yobs Y1₁ Y0₁ Y0)
    (hY0₁ : ∀ s, Y0₁ s = factorOutcome δ θ lam Z₁ μ₁ s)
    (hY0 : ∀ j s, Y0 j s = factorOutcome δ θ lam (Z j) (μ j) s)
    (w : J → ℝ) (hw : ∑ j, w j = 1) (hZ : ∑ j, w j • Z j = Z₁)
    (hfit : preLoss (fun t : Tpre => Yobs₁ (.inl t)) (fun j t => Yobs j (.inl t)) w = 0)
    (hrank : ∀ d : F → ℝ, (∀ t : Tpre, lam (.inl t) ⬝ᵥ d = 0) → d = 0) (t : Tpost) :
    effectHat Yobs₁ Yobs w (.inr t) = Y1₁ t - Y0₁ (.inr t) := by
  have hY0' : Y0 = fun j => factorOutcome δ θ lam (Z j) (μ j) :=
    funext fun j => funext (hY0 j)
  have hfit' := (hcons.preLoss_eq_zero_iff w).mp hfit
  have hpre : ∀ s ∈ (Finset.univ.map Function.Embedding.inl : Finset (Tpre ⊕ Tpost)),
      factorOutcome δ θ lam Z₁ μ₁ s
        = synth w (fun j => factorOutcome δ θ lam (Z j) (μ j)) s := by
    intro s hs
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hs
    rw [← hY0₁, ← hY0']
    exact hfit' u
  have hrank' : ∀ d : F → ℝ,
      (∀ s ∈ (Finset.univ.map Function.Embedding.inl : Finset (Tpre ⊕ Tpost)),
        lam s ⬝ᵥ d = 0) → d = 0 :=
    fun d hd => hrank d fun u => hd _ (Finset.mem_map_of_mem _ (Finset.mem_univ u))
  have h0 := factorOutcome_sub_synth_eq_zero_of_preFit δ θ lam Z₁ μ₁ Z μ w _ hw hZ hpre hrank'
    (.inr t)
  have hb := hcons.effectHat_sub_effect w t
  rw [← hY0₁, ← hY0'] at h0
  linarith

/-- `effectHat_eq_effect_of_preFit` with the rank condition stated as invertibility of the
pre-treatment factor matrix `∑_{t ∈ Tpre} lam tᵀ lam t`. -/
theorem effectHat_eq_effect_of_preFit_of_isUnit {Tpre Tpost : Type*} [Fintype Tpre]
    [DecidableEq F]
    (δ : Tpre ⊕ Tpost → ℝ) (θ : Tpre ⊕ Tpost → R → ℝ) (lam : Tpre ⊕ Tpost → F → ℝ)
    (Z₁ : R → ℝ) (μ₁ : F → ℝ) (Z : J → R → ℝ) (μ : J → F → ℝ)
    (Yobs₁ : Tpre ⊕ Tpost → ℝ) (Yobs : J → Tpre ⊕ Tpost → ℝ) (Y1₁ : Tpost → ℝ)
    (Y0₁ : Tpre ⊕ Tpost → ℝ) (Y0 : J → Tpre ⊕ Tpost → ℝ)
    (hcons : PanelConsistent Yobs₁ Yobs Y1₁ Y0₁ Y0)
    (hY0₁ : ∀ s, Y0₁ s = factorOutcome δ θ lam Z₁ μ₁ s)
    (hY0 : ∀ j s, Y0 j s = factorOutcome δ θ lam (Z j) (μ j) s)
    (w : J → ℝ) (hw : ∑ j, w j = 1) (hZ : ∑ j, w j • Z j = Z₁)
    (hfit : preLoss (fun t : Tpre => Yobs₁ (.inl t)) (fun j t => Yobs j (.inl t)) w = 0)
    (hrank : IsUnit (factorGram (Finset.univ.map Function.Embedding.inl) lam)) (t : Tpost) :
    effectHat Yobs₁ Yobs w (.inr t) = Y1₁ t - Y0₁ (.inr t) := by
  refine effectHat_eq_effect_of_preFit δ θ lam Z₁ μ₁ Z μ Yobs₁ Yobs Y1₁ Y0₁ Y0 hcons hY0₁ hY0
    w hw hZ hfit (fun d hd => (isUnit_factorGram_iff _ lam).mp hrank d fun s hs => ?_) t
  obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hs
  exact hd u

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
