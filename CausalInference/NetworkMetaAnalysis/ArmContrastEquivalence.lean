/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.NetworkModel
public import CausalInference.NetworkMetaAnalysis.Pooling

/-!
# Network meta-analysis: the arm based and the contrast based estimates coincide

The arm based fixed effect model has arm estimates `y` with means `μ_j + d̃_k - d̃_{base j}`
(`armDesign`, free study intercepts `μ_j`) and a positive definite covariance `V`. The contrast
based model uses the baseline shifted contrasts `L y`, `(L y)_e = y_{jk} - y_{j, base j}`
(`armContrastMatrix`), whose means are `X_c d` for the reduced design `X_c` of the within-study
contrasts (`armContrastDesign`) and whose covariance is `C = L V Lᵀ` (the
`covMatrix_matrix_mulVec`).

**The estimates coincide** (`glsEstimate_armDesign_inr`): for a connected
network and every positive definite `V`, the relative effect part of the arm based generalized
least squares estimate is the generalized least squares estimate of the contrast model,
`β̂_arm(y)_d = (X_cᵀ C⁻¹ X_c)⁻¹ X_cᵀ C⁻¹ L y`, and the study intercepts are
`μ̂_j = y_{j, base j} - (V Lᵀ C⁻¹ (L y - X_c d̂))_{j, base j}`. No block structure of `V` is
needed: the intercepts are free, so profiling them out leaves the marginal model of the
contrasts. The proof verifies the normal equations of the arm model at the candidate built from
the contrast estimate: its residual is `V Lᵀ C⁻¹ (L y - X_c d̂)`, and `Xᵀ Lᵀ = (L X)ᵀ` kills the
contrast normal equations because `L X (μ, d) = X_c d` (`armContrastMatrix_mulVec_armDesign`).

**Invariance under an invertible reparameterization of the data**
(`glsEstimate_reparam`): for `T` with a two sided inverse and `V` invertible,
`β̂(T X, T V Tᵀ, T y) = β̂(X, V, y)`.

**The two models as linear models** (`armModel_contrastModel`): if the arm estimates follow the
arm based linear model, the contrasts follow the contrast based linear model with design `X_c`
and covariance `L V Lᵀ`, and the two estimates of the basic parameters are equal for every
outcome.

## Main definitions

* `armContrastMatrix`, `armContrastDesign`, `armModelResidual`.

## Main results

* `glsEstimate_reparam`, `gram_mulVec_glsEstimate`.
* `armContrastMatrix_mulVec`, `armContrastMatrix_mulVec_armDesign`,
  `vecMul_armContrastMatrix_injective`, `posDef_armContrastMatrix_mul_mul_transpose`,
  `armContrastDesign_injective`.
* `glsEstimate_armDesign_eq`, `glsEstimate_armDesign_inr`, `glsEstimate_armDesign_inl`,
  `armModel_contrastModel`.

## References

The model with study baselines and basic parameters is that of

* G. Lu and A. E. Ades, *Combination of direct and indirect evidence in mixed treatment
  comparisons*, Statistics in Medicine 23 (2004).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix MeasureTheory ProbabilityTheory BiasAnalysis.MeasurementError

/-! ### Two facts about generalized least squares -/

section General

variable {n m p : Type*} [Fintype n] [Fintype m] [Fintype p] [DecidableEq n] [DecidableEq m]
  [DecidableEq p]

/-- **Generalized least squares is invariant under an invertible reparameterization of the
data**: if `S T = 1`, `T S = 1` and `V` is invertible, then
`β̂(T X, T V Tᵀ, T y) = β̂(X, V, y)`. -/
theorem glsEstimate_reparam {T : Matrix m n ℝ} {S : Matrix n m ℝ} (hST : S * T = 1)
    (hTS : T * S = 1) {V : Matrix n n ℝ} (hV : IsUnit V.det) (X : Matrix n p ℝ) (y : n → ℝ) :
    glsEstimate (T * X) (T * V * Tᵀ) (T *ᵥ y) = glsEstimate X V y := by
  have hinv : (T * V * Tᵀ)⁻¹ = Sᵀ * V⁻¹ * S := by
    refine inv_eq_left_inv ?_
    calc Sᵀ * V⁻¹ * S * (T * V * Tᵀ) = Sᵀ * V⁻¹ * (S * T) * V * Tᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Sᵀ * Tᵀ := by
          rw [hST, Matrix.mul_one, Matrix.mul_assoc Sᵀ, nonsing_inv_mul _ hV, Matrix.mul_one]
      _ = 1 := by rw [← transpose_mul, hTS, transpose_one]
  have hSTt : Tᵀ * Sᵀ = 1 := by rw [← transpose_mul, hST, transpose_one]
  have hgram : (T * X)ᵀ * (T * V * Tᵀ)⁻¹ * (T * X) = Xᵀ * V⁻¹ * X := by
    rw [hinv, transpose_mul]
    calc Xᵀ * Tᵀ * (Sᵀ * V⁻¹ * S) * (T * X) = Xᵀ * (Tᵀ * Sᵀ) * V⁻¹ * (S * T) * X := by
          simp only [Matrix.mul_assoc]
      _ = Xᵀ * V⁻¹ * X := by rw [hSTt, hST, Matrix.mul_one, Matrix.mul_one]
  have hrhs : (T * X)ᵀ * (T * V * Tᵀ)⁻¹ * T = Xᵀ * V⁻¹ := by
    rw [hinv, transpose_mul]
    calc Xᵀ * Tᵀ * (Sᵀ * V⁻¹ * S) * T = Xᵀ * (Tᵀ * Sᵀ) * V⁻¹ * (S * T) := by
          simp only [Matrix.mul_assoc]
      _ = Xᵀ * V⁻¹ := by rw [hSTt, hST, Matrix.mul_one, Matrix.mul_one]
  rw [glsEstimate, glsEstimate, glsMatrix, glsMatrix, mulVec_mulVec, hgram, Matrix.mul_assoc _ _ T,
    Matrix.mul_assoc (Xᵀ * V⁻¹ * X)⁻¹, ← Matrix.mul_assoc (T * X)ᵀ, hrhs, ← Matrix.mul_assoc]

/-- **The normal equations of the estimate**: `(Xᵀ V⁻¹ X) β̂ = Xᵀ V⁻¹ y` when `Xᵀ V⁻¹ X` is
invertible. -/
theorem gram_mulVec_glsEstimate {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hM : IsUnit (Xᵀ * V⁻¹ * X)) (y : n → ℝ) :
    (Xᵀ * V⁻¹ * X) *ᵥ glsEstimate X V y = Xᵀ *ᵥ (V⁻¹ *ᵥ y) := by
  rw [glsEstimate, glsMatrix, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hM), Matrix.one_mul, mulVec_mulVec]

end General

/-! ### The baseline shifted contrasts -/

section Contrasts

variable {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
  {arms : J → Finset K} {base : J → K}

/-- The **baseline shift contrast matrix** `L`: row `e = (j, k)` has `+1` in the column of the
arm `(j, k)` and `-1` in the column of the baseline arm `(j, base j)`, so
`(L y)_e = y_{jk} - y_{j, base j}`. -/
def armContrastMatrix (hbase : ∀ j, base j ∈ arms j) :
    Matrix (ArmContrast arms base) (ArmIndex arms) ℝ :=
  Matrix.of fun e a => (if a = e.1 then 1 else 0) -
    (if a = ⟨(e.1.1.1, base e.1.1.1), hbase _⟩ then 1 else 0)

/-- The **contrast based design**: the reduced design of the within-study contrasts
`base j → k`. -/
def armContrastDesign (arms : J → Finset K) (base : J → K) (r : K) :
    Matrix (ArmContrast arms base) {k // k ≠ r} ℝ :=
  reducedDesign (fun e : ArmContrast arms base => base e.1.1.1) (fun e => e.1.1.2) r

/-- `(L y)_e = y_{jk} - y_{j, base j}`. -/
theorem armContrastMatrix_mulVec (hbase : ∀ j, base j ∈ arms j) (θ : ArmIndex arms → ℝ)
    (e : ArmContrast arms base) :
    (armContrastMatrix hbase *ᵥ θ) e = θ e.1 - θ ⟨(e.1.1.1, base e.1.1.1), hbase _⟩ := by
  classical
  simp [armContrastMatrix, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

/-- **The contrasts of the arm means are the contrast design**: `L X (μ, d) = X_c d`. -/
theorem armContrastMatrix_mulVec_armDesign (hbase : ∀ j, base j ∈ arms j) (r : K)
    (β : J ⊕ {k // k ≠ r} → ℝ) :
    armContrastMatrix hbase *ᵥ (armDesign arms base r *ᵥ β) =
      armContrastDesign arms base r *ᵥ (β ∘ Sum.inr) := by
  funext e
  rw [armContrastMatrix_mulVec, armDesign_mulVec_contrast, armDesign_mulVec_base,
    armContrastDesign]
  ring

/-- The rows of `L` are linearly independent: each contrast is the only one involving its own
non-baseline arm. -/
theorem vecMul_armContrastMatrix_injective (hbase : ∀ j, base j ∈ arms j) :
    Function.Injective (armContrastMatrix hbase).vecMul := by
  classical
  intro x x' h
  funext e₀
  have h0 : (x ᵥ* armContrastMatrix hbase) e₀.1 = (x' ᵥ* armContrastMatrix hbase) e₀.1 :=
    congrFun h e₀.1
  have key : ∀ z : ArmContrast arms base → ℝ, (z ᵥ* armContrastMatrix hbase) e₀.1 = z e₀ := by
    intro z
    simp only [vecMul, dotProduct, armContrastMatrix, Matrix.of_apply]
    rw [Fintype.sum_eq_single e₀]
    · have hne : e₀.1 ≠ ⟨(e₀.1.1.1, base e₀.1.1.1), hbase _⟩ := fun h' =>
        e₀.2 (congrArg (fun a : ArmIndex arms => a.1.2) h')
      simp [hne]
    · intro e he
      have h1 : e₀.1 ≠ e.1 := fun h' => he (Subtype.ext h'.symm)
      have h2 : e₀.1 ≠ ⟨(e.1.1.1, base e.1.1.1), hbase _⟩ := fun h' =>
        e₀.2 (by
          have := congrArg (fun a : ArmIndex arms => a.1) h'
          have h3 := congrArg Prod.snd this
          have h4 := congrArg Prod.fst this
          simp only at h3 h4
          rw [h3, h4])
      simp [h1, h2]
  rw [key, key] at h0
  exact h0

/-- The covariance `C = L V Lᵀ` of the contrasts is positive definite for `V` positive
definite. -/
theorem posDef_armContrastMatrix_mul_mul_transpose (hbase : ∀ j, base j ∈ arms j)
    {V : Matrix (ArmIndex arms) (ArmIndex arms) ℝ} (hV : V.PosDef) :
    (armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ).PosDef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using
    hV.mul_mul_conjTranspose_same (vecMul_armContrastMatrix_injective hbase)

omit [Fintype J] [DecidableEq J] in
/-- The contrast design has full column rank exactly for a connected network. -/
theorem armContrastDesign_injective (r : K) (hcon : (armContrastGraph arms base).Connected) :
    Function.Injective (armContrastDesign arms base r).mulVec :=
  (reducedDesign_injective_iff _ _ r).2 hcon

end Contrasts

/-! ### The equality of the arm based and the contrast based estimates -/

section Equality

variable {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
  {arms : J → Finset K} {base : J → K}

/-- The **residual of the arm model at the contrast estimate**: `V Lᵀ C⁻¹ (L y - X_c d̂)` with
`C = L V Lᵀ` and `d̂` the contrast based estimate. It vanishes on the contrasts after applying
`L` up to the fitted contrasts, and its baseline entries adjust the study intercepts. -/
noncomputable def armModelResidual (hbase : ∀ j, base j ∈ arms j) (r : K)
    (V : Matrix (ArmIndex arms) (ArmIndex arms) ℝ) (y : ArmIndex arms → ℝ) :
    ArmIndex arms → ℝ :=
  V *ᵥ ((armContrastMatrix hbase)ᵀ *ᵥ
    ((armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ)⁻¹ *ᵥ
      (armContrastMatrix hbase *ᵥ y - armContrastDesign arms base r *ᵥ
        glsEstimate (armContrastDesign arms base r)
          (armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ)
          (armContrastMatrix hbase *ᵥ y))))

/-- **The arm based estimate in closed form through the contrast based estimate**: for a
connected network and a positive definite `V`, `β̂_arm(y) = (μ̂, d̂)` with `d̂` the contrast
based estimate and `μ̂_j = y_{j, base j} - (V Lᵀ C⁻¹ (L y - X_c d̂))_{j, base j}`. -/
theorem glsEstimate_armDesign_eq (hbase : ∀ j, base j ∈ arms j) (r : K)
    (hcon : (armContrastGraph arms base).Connected)
    {V : Matrix (ArmIndex arms) (ArmIndex arms) ℝ} (hV : V.PosDef) (y : ArmIndex arms → ℝ) :
    glsEstimate (armDesign arms base r) V y =
      Sum.elim (fun j => (y - armModelResidual hbase r V y) ⟨(j, base j), hbase j⟩)
        (glsEstimate (armContrastDesign arms base r)
          (armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ)
          (armContrastMatrix hbase *ᵥ y)) := by
  have hCpd := posDef_armContrastMatrix_mul_mul_transpose hbase hV
  have hCu : IsUnit (armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ).det :=
    (isUnit_iff_isUnit_det _).1 hCpd.isUnit
  have hMc := isUnit_gram_inv hCpd (armContrastDesign_injective r hcon)
  obtain ⟨dhat, hdhat⟩ : ∃ d : {k // k ≠ r} → ℝ, d = glsEstimate (armContrastDesign arms base r)
      (armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ)
      (armContrastMatrix hbase *ᵥ y) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ArmContrast arms base → ℝ,
      s = (armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ)⁻¹ *ᵥ
      (armContrastMatrix hbase *ᵥ y - armContrastDesign arms base r *ᵥ dhat) := ⟨_, rfl⟩
  have hres : armModelResidual hbase r V y = V *ᵥ ((armContrastMatrix hbase)ᵀ *ᵥ s) := by
    rw [armModelResidual, ← hdhat, ← hs]
  rw [← hdhat, hres]
  -- the contrast normal equations
  have hnorm : (armContrastDesign arms base r)ᵀ *ᵥ s = 0 := by
    have h := gram_mulVec_glsEstimate hMc (armContrastMatrix hbase *ᵥ y)
    rw [← hdhat] at h
    have e : (armContrastDesign arms base r)ᵀ *ᵥ
        ((armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ)⁻¹ *ᵥ
          (armContrastDesign arms base r *ᵥ dhat)) =
        ((armContrastDesign arms base r)ᵀ *
          (armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ)⁻¹ *
            armContrastDesign arms base r) *ᵥ dhat := by
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    rw [hs, mulVec_sub, mulVec_sub, e, h, sub_self]
  -- the contrasts of the fitted arm means
  have hLθ : armContrastMatrix hbase *ᵥ (y - V *ᵥ ((armContrastMatrix hbase)ᵀ *ᵥ s)) =
      armContrastDesign arms base r *ᵥ dhat := by
    have e1 : armContrastMatrix hbase *ᵥ (V *ᵥ ((armContrastMatrix hbase)ᵀ *ᵥ s)) =
        armContrastMatrix hbase *ᵥ y - armContrastDesign arms base r *ᵥ dhat := by
      rw [mulVec_mulVec, mulVec_mulVec, hs, mulVec_mulVec, mul_nonsing_inv _ hCu, one_mulVec]
    rw [mulVec_sub, e1, sub_sub_cancel]
  -- the candidate reproduces the fitted arm means
  set θ := y - V *ᵥ ((armContrastMatrix hbase)ᵀ *ᵥ s) with hθ
  have hXβ : armDesign arms base r *ᵥ Sum.elim (fun j => θ ⟨(j, base j), hbase j⟩) dhat = θ := by
    funext a
    by_cases ha : a.1.2 = base a.1.1
    · have : a = ⟨(a.1.1, base a.1.1), hbase _⟩ := Subtype.ext (Prod.ext rfl ha)
      rw [this, armDesign_mulVec_base]
      rfl
    · have h1 := armDesign_mulVec_contrast arms base r
        (Sum.elim (fun j => θ ⟨(j, base j), hbase j⟩) dhat) ⟨a, ha⟩
      have h2 := congrFun hLθ ⟨a, ha⟩
      rw [armContrastMatrix_mulVec] at h2
      simp only [Sum.elim_inl, Sum.elim_comp_inr] at h1
      rw [h1, ← armContrastDesign, ← h2]
      ring
  -- `Xᵀ Lᵀ s = 0`
  have hzero : (armDesign arms base r)ᵀ *ᵥ ((armContrastMatrix hbase)ᵀ *ᵥ s) = 0 := by
    have key : ∀ β, β ⬝ᵥ ((armDesign arms base r)ᵀ *ᵥ ((armContrastMatrix hbase)ᵀ *ᵥ s)) = 0 := by
      intro β
      rw [dotProduct_mulVec, vecMul_transpose, dotProduct_mulVec, vecMul_transpose,
        armContrastMatrix_mulVec_armDesign]
      have e : (armContrastDesign arms base r *ᵥ (β ∘ Sum.inr)) ⬝ᵥ s =
          (β ∘ Sum.inr) ⬝ᵥ ((armContrastDesign arms base r)ᵀ *ᵥ s) := by
        rw [dotProduct_mulVec, vecMul_transpose]
      rw [e, hnorm, dotProduct_zero]
    funext c
    have := key (Pi.single c 1)
    rwa [single_dotProduct, one_mul] at this
  refine glsEstimate_eq_of_normal (isUnit_gram_inv hV ((armDesign_injective_iff hbase r).2 hcon)) ?_
  have hVu : IsUnit V.det := (isUnit_iff_isUnit_det _).1 hV.isUnit
  have e : V⁻¹ *ᵥ (V *ᵥ ((armContrastMatrix hbase)ᵀ *ᵥ s)) = (armContrastMatrix hbase)ᵀ *ᵥ s := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hVu, one_mulVec]
  rw [← mulVec_mulVec, ← mulVec_mulVec, hXβ, hθ, mulVec_sub, e, mulVec_sub, hzero, sub_zero]

/-- **The arm based and the contrast based estimates coincide.** For a
connected network of studies that contain their baseline arms and a positive definite arm
covariance `V`, the relative effect part of the arm based generalized least squares estimate is
the generalized least squares estimate of the contrast model with the baseline shifted contrasts
`L y` and their induced covariance `L V Lᵀ`. -/
theorem glsEstimate_armDesign_inr (hbase : ∀ j, base j ∈ arms j) (r : K)
    (hcon : (armContrastGraph arms base).Connected)
    {V : Matrix (ArmIndex arms) (ArmIndex arms) ℝ} (hV : V.PosDef) (y : ArmIndex arms → ℝ) :
    (fun k => glsEstimate (armDesign arms base r) V y (Sum.inr k)) =
      glsEstimate (armContrastDesign arms base r)
        (armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ)
        (armContrastMatrix hbase *ᵥ y) := by
  rw [glsEstimate_armDesign_eq hbase r hcon hV y]
  rfl

/-- **The study intercepts of the arm based estimate**: `μ̂_j` is the baseline arm estimate minus
the baseline entry of the residual `V Lᵀ C⁻¹ (L y - X_c d̂)`. -/
theorem glsEstimate_armDesign_inl (hbase : ∀ j, base j ∈ arms j) (r : K)
    (hcon : (armContrastGraph arms base).Connected)
    {V : Matrix (ArmIndex arms) (ArmIndex arms) ℝ} (hV : V.PosDef) (y : ArmIndex arms → ℝ)
    (j : J) :
    glsEstimate (armDesign arms base r) V y (Sum.inl j) =
      y ⟨(j, base j), hbase j⟩ - armModelResidual hbase r V y ⟨(j, base j), hbase j⟩ := by
  rw [glsEstimate_armDesign_eq hbase r hcon hV y]
  rfl

/-- **The arm based and the contrast based linear models.** If the arm estimates follow the arm
based linear model with design `X` and covariance `V`, then for any fixed study intercepts `μ₀`
the baseline shifted contrasts `L y` follow the contrast based linear model with design `X_c`
and covariance `L V Lᵀ` (their law does not depend on `μ₀`), and for a connected network and
`V` positive definite the two estimates of the basic parameters are equal at every outcome. -/
theorem armModel_contrastModel {Ω : Type*} [MeasurableSpace Ω] (hbase : ∀ j, base j ∈ arms j)
    {r : K} {P : (J ⊕ {k // k ≠ r} → ℝ) → Measure Ω} {Y : ArmIndex arms → Ω → ℝ}
    {V : Matrix (ArmIndex arms) (ArmIndex arms) ℝ}
    (h : IsLinearModel (ArmIndex arms) P Y (armDesign arms base r) V) (μ₀ : J → ℝ) :
    IsLinearModel (ArmContrast arms base) (fun d => P (Sum.elim μ₀ d))
        (fun e ω => (armContrastMatrix hbase *ᵥ fun a => Y a ω) e) (armContrastDesign arms base r)
        (armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ) ∧
      (V.PosDef → (armContrastGraph arms base).Connected → ∀ ω,
        (fun k => glsEstimate (armDesign arms base r) V (fun a => Y a ω) (Sum.inr k)) =
          glsEstimate (armContrastDesign arms base r)
            (armContrastMatrix hbase * V * (armContrastMatrix hbase)ᵀ)
            (fun e => (armContrastMatrix hbase *ᵥ fun a => Y a ω) e)) := by
  refine ⟨⟨fun d => h.isProbabilityMeasure _, fun d e => memLp_matrix_mulVec (h.memLp _) _ e,
    fun d e => ?_, fun d => h.covMatrix_mulVec _ _⟩, fun hV hcon ω => ?_⟩
  · rw [h.integral_mulVec, ← mulVec_mulVec, armContrastMatrix_mulVec_armDesign, Sum.elim_comp_inr]
  · exact glsEstimate_armDesign_inr hbase r hcon hV _

end Equality

end NetworkMetaAnalysis

end CausalInference
