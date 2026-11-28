/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.RestrictedContrast
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The restricted likelihood does not depend on the choice of error contrasts

In the linear model `y ~ N(X β, V)` with `X` of full column rank `p` and `n = m + p`
observations, any two `n × m` contrast matrices `K₁`, `K₂` of rank `m` with `Kᵢᵀ X = 0` have the
same column space, the orthogonal complement of the column space of `X`. Hence
`K₂ = K₁ T` for an invertible `T` (`exists_contrast_change`), and by `contrastLogLik_mul` the two
restricted log likelihoods differ by the constant `-log |det T|`, which depends neither on the
covariance `V` nor on the data (`contrastLogLik_eq_add_of_contrast`). A parameter value maximizes
one restricted likelihood exactly when it maximizes the other
(`isMaxOn_contrastLogLik_iff`): the restricted maximum likelihood estimate is the same for every
full set of error contrasts (Harville 1974).

## Main results

* `rank_eq_card_of_det_ne_zero`: `det(Kᵀ K) ≠ 0` gives full column rank.
* `exists_contrast_change`, `contrastLogLik_eq_add_of_contrast`, `isMaxOn_contrastLogLik_iff`.
* `example_contrast_change`: an instance with two observations and the mean as fixed effect.

## References

* D. A. Harville, *Bayesian inference for variance components using only error contrasts*,
  Biometrika 61 (1974).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open Matrix

variable {n m p : Type*} [Fintype n] [Fintype m] [Fintype p] [DecidableEq m]

/-- **A nonzero Gram determinant gives full column rank**: `det(Kᵀ K) ≠ 0` implies
`rank K = card m`. -/
theorem rank_eq_card_of_det_ne_zero {K : Matrix n m ℝ} (hK : (Kᵀ * K).det ≠ 0) :
    K.rank = Fintype.card m := by
  rw [← rank_transpose_mul_self, rank_of_isUnit _ ((isUnit_iff_isUnit_det _).2
    (isUnit_iff_ne_zero.2 hK))]

/-- **Two full rank contrast matrices differ by an invertible factor**: if `X` has rank
`card p`, `card m + card p = card n`, and `K₁`, `K₂` have rank `card m` with `K₁ᵀ X = 0` and
`K₂ᵀ X = 0`, then `K₂ = K₁ T` for some `T` with `det T` a unit. Proof: both column spaces lie in
the kernel of `Xᵀ`, of dimension `card n - card p = card m`, hence equal it; the columns of
`K₂` are therefore combinations of those of `K₁`, and `rank T ≥ rank K₂ = card m`. -/
theorem exists_contrast_change {X : Matrix n p ℝ} (hX : X.rank = Fintype.card p)
    (hm : Fintype.card m + Fintype.card p = Fintype.card n) {K₁ K₂ : Matrix n m ℝ}
    (h1 : K₁.rank = Fintype.card m) (h2 : K₂.rank = Fintype.card m)
    (h1X : K₁ᵀ * X = 0) (h2X : K₂ᵀ * X = 0) :
    ∃ T : Matrix m m ℝ, IsUnit T.det ∧ K₂ = K₁ * T := by
  classical
  set W := LinearMap.ker Xᵀ.mulVecLin with hWdef
  have hle : ∀ K : Matrix n m ℝ, Kᵀ * X = 0 → LinearMap.range K.mulVecLin ≤ W := by
    rintro K hK _ ⟨u, rfl⟩
    have : Xᵀ * K = 0 := by
      have h := congrArg Matrix.transpose hK
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, this,
      Matrix.zero_mulVec, W]
  have hW : Module.finrank ℝ W = Fintype.card m := by
    have := LinearMap.finrank_range_add_finrank_ker Xᵀ.mulVecLin
    have hr : Module.finrank ℝ (LinearMap.range Xᵀ.mulVecLin) = Fintype.card p := by
      rw [← Matrix.rank, Matrix.rank_transpose, hX]
    rw [← hWdef, hr, Module.finrank_fintype_fun_eq_card] at this
    omega
  have hrange : ∀ K : Matrix n m ℝ, Kᵀ * X = 0 → K.rank = Fintype.card m →
      LinearMap.range K.mulVecLin = W := fun K hK hr =>
    Submodule.eq_of_le_of_finrank_eq (hle K hK) (by rw [← Matrix.rank, hr, hW])
  have hG : IsUnit (K₁ᵀ * K₁) := by
    rw [← Matrix.mulVec_surjective_iff_isUnit, Matrix.mulVec_surjective_iff_rank_eq_card,
      Matrix.rank_transpose_mul_self, h1]
  have hGd : IsUnit (K₁ᵀ * K₁).det := (Matrix.isUnit_iff_isUnit_det _).1 hG
  set T := (K₁ᵀ * K₁)⁻¹ * K₁ᵀ * K₂ with hTdef
  have hKT : K₁ * T = K₂ := by
    refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
    simp only [Matrix.toLin'_apply]
    have hu : K₂ *ᵥ u ∈ LinearMap.range K₁.mulVecLin := by
      rw [hrange K₁ h1X h1, ← hrange K₂ h2X h2]
      exact ⟨u, rfl⟩
    obtain ⟨w, hw⟩ := hu
    simp only [Matrix.mulVecLin_apply] at hw
    have hTu : T *ᵥ u = w := by
      rw [hTdef, ← Matrix.mulVec_mulVec, ← hw, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hGd, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hTu, hw]
  refine ⟨T, ?_, hKT.symm⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit,
    Matrix.mulVec_surjective_iff_rank_eq_card]
  refine le_antisymm (Matrix.rank_le_card_width T) ?_
  calc Fintype.card m = K₂.rank := h2.symm
    _ = (K₁ * T).rank := by rw [hKT]
    _ ≤ T.rank := Matrix.rank_mul_le_right _ _

/-- **The two restricted likelihoods differ by a constant**: under the hypotheses of
`exists_contrast_change`, there is a constant `c` such that for every positive definite `V` and
every `y`, `contrastLogLik K₂ V y = contrastLogLik K₁ V y + c`. The constant depends neither on
the covariance nor on the data. -/
theorem contrastLogLik_eq_add_of_contrast {X : Matrix n p ℝ}
    (hX : X.rank = Fintype.card p) (hm : Fintype.card m + Fintype.card p = Fintype.card n)
    {K₁ K₂ : Matrix n m ℝ} (h1 : K₁.rank = Fintype.card m) (h2 : K₂.rank = Fintype.card m)
    (h1X : K₁ᵀ * X = 0) (h2X : K₂ᵀ * X = 0) :
    ∃ c : ℝ, ∀ V : Matrix n n ℝ, V.PosDef → ∀ y : n → ℝ,
      contrastLogLik K₂ V y = contrastLogLik K₁ V y + c := by
  classical
  obtain ⟨T, hT, rfl⟩ := exists_contrast_change hX hm h1 h2 h1X h2X
  have hinj : Function.Injective K₁.mulVec := by
    have := LinearMap.finrank_range_add_finrank_ker K₁.mulVecLin
    rw [← Matrix.rank, h1, Module.finrank_fintype_fun_eq_card] at this
    have hk : LinearMap.ker K₁.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    exact LinearMap.ker_eq_bot.1 hk
  refine ⟨-Real.log |T.det|, fun V hV y => ?_⟩
  have hA : (K₁ᵀ * V * K₁).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.conjTranspose_mul_mul_same hinj
  rw [contrastLogLik_mul K₁ V hT.ne_zero hA.det_pos.ne' y]
  ring

/-- **The maximizers coincide**: under the hypotheses of `exists_contrast_change`, for every
family `V θ` of positive definite matrices, every set `S` of parameters and every `y`,
`θ₀` maximizes `θ ↦ contrastLogLik K₁ (V θ) y` on `S` exactly when it maximizes
`θ ↦ contrastLogLik K₂ (V θ) y` on `S`. -/
theorem isMaxOn_contrastLogLik_iff {Θ : Type*} {X : Matrix n p ℝ}
    (hX : X.rank = Fintype.card p) (hm : Fintype.card m + Fintype.card p = Fintype.card n)
    {K₁ K₂ : Matrix n m ℝ} (h1 : K₁.rank = Fintype.card m) (h2 : K₂.rank = Fintype.card m)
    (h1X : K₁ᵀ * X = 0) (h2X : K₂ᵀ * X = 0) {V : Θ → Matrix n n ℝ} (hV : ∀ θ, (V θ).PosDef)
    (y : n → ℝ) (S : Set Θ) (θ₀ : Θ) :
    IsMaxOn (fun θ => contrastLogLik K₁ (V θ) y) S θ₀ ↔
      IsMaxOn (fun θ => contrastLogLik K₂ (V θ) y) S θ₀ := by
  obtain ⟨c, hc⟩ := contrastLogLik_eq_add_of_contrast hX hm h1 h2 h1X h2X
  simp only [isMaxOn_iff, hc _ (hV _)]
  constructor <;> intro h θ hθ <;> linarith [h θ hθ]

/-- **An instance**: two observations, the mean as the only fixed effect (`X = 1`), the
contrasts `K₁ = (1, -1)ᵀ` and `K₂ = (2, -2)ᵀ`, and the covariances `diag(1 + t, 2 + t)`,
`t ≥ 0`. All hypotheses of `isMaxOn_contrastLogLik_iff` hold. -/
theorem example_contrast_change :
    let X : Matrix (Fin 2) (Fin 1) ℝ := of fun _ _ => 1
    let K₁ : Matrix (Fin 2) (Fin 1) ℝ := of fun i _ => ![1, -1] i
    let K₂ : Matrix (Fin 2) (Fin 1) ℝ := of fun i _ => ![2, -2] i
    let V : Set.Ici (0 : ℝ) → Matrix (Fin 2) (Fin 2) ℝ :=
      fun t => diagonal ![1 + (t : ℝ), 2 + (t : ℝ)]
    X.rank = Fintype.card (Fin 1) ∧ Fintype.card (Fin 1) + Fintype.card (Fin 1) =
      Fintype.card (Fin 2) ∧ K₁.rank = Fintype.card (Fin 1) ∧
      K₂.rank = Fintype.card (Fin 1) ∧ K₁ᵀ * X = 0 ∧ K₂ᵀ * X = 0 ∧ ∀ t, (V t).PosDef := by
  intro X K₁ K₂ V
  refine ⟨rank_eq_card_of_det_ne_zero ?_, rfl, rank_eq_card_of_det_ne_zero ?_,
    rank_eq_card_of_det_ne_zero ?_, ?_, ?_, fun t => ?_⟩
  · rw [det_unique]; simp [X, Matrix.mul_apply]
  · rw [det_unique]; norm_num [K₁, Matrix.mul_apply, Fin.sum_univ_two, Function.swap]
  · rw [det_unique]; norm_num [K₂, Matrix.mul_apply, Fin.sum_univ_two, Function.swap]
  · ext i j; simp [K₁, X, Matrix.mul_apply, Fin.sum_univ_two, Function.swap]
  · ext i j; simp [K₂, X, Matrix.mul_apply, Fin.sum_univ_two, Function.swap]
  · rw [posDef_diagonal_iff]
    intro i
    have ht : (0 : ℝ) ≤ t := t.2
    fin_cases i <;> simp <;> linarith

end MetaAnalysis

end CausalInference
