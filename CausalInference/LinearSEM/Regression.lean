/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Population least squares from a covariance matrix

Let `C : Matrix V V ℝ` be the covariance matrix of a finite family of variables `X v`. The
population least squares regression of `X y` on the variables `X s`, `s ∈ S`, has coefficient
vector `β` (supported on `S`) solving the normal equations `∑ t, C s t β t = C s y` for `s ∈ S`,
that is `C_SS β_S = C_Sy`. Everything is stated at the level of second moments.

## Main definitions

* `IsRegCoeff C S y β`: `β` is supported on `S` and solves the normal equations.
* `regCoeff C S y`: the vector `C_SS⁻¹ C_Sy`, extended by zero outside `S`.
* `covComb C a b`: the covariance `aᵀ C b` of two linear combinations `a ⬝ X` and `b ⬝ X`.
* `residual y β`: the coefficient vector of the residual `X y - β ⬝ X`.
* `partialCov C Z x y`: the partial covariance of `X x` and `X y` given `X_Z`, the Schur
  complement entry `C x y - C_xZ C_ZZ⁻¹ C_Zy`.

## Main results

* `isRegCoeff_iff_orthogonal`: the normal equations say that the residual is uncorrelated with
  every regressor (the orthogonality principle, Primer Section 1.3.11).
* `IsRegCoeff.residual_variance_le`: a solution of the normal equations minimizes the residual
  variance over all coefficient vectors supported on `S` (population least squares).
* `IsRegCoeff.unique`, `regCoeff_isRegCoeff`, `isRegCoeff_iff_eq_regCoeff`: when `C_SS` is
  invertible the normal equations have exactly one solution, `regCoeff C S y`;
  `isUnit_submatrix_of_posDef`: this holds for every `S` when `C` is positive definite.
* `isRegCoeff_singleton_iff`: the simple slope `r_YX = C x y / C x x` (Primer equation 1.22).
* `isRegCoeff_pair_iff`: the two regressor formulas (Primer equations 1.27 and 1.28).
* `IsRegCoeff.eq_zero_iff_partialCov_eq_zero`: the coefficient of `x` in the regression of `y` on
  `x` and `Z` vanishes if and only if the partial covariance of `x` and `y` given `Z` vanishes;
  `isRegCoeff_pair_fst_eq_zero_iff` gives the explicit form for one covariate.

Source: J. Pearl, M. Glymour and N. P. Jewell (2016), *Causal Inference in Statistics: A Primer*,
Sections 1.3.10 and 1.3.11, equations (1.22), (1.24), (1.27), (1.28).
-/

@[expose] public section

namespace CausalInference

open Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `β` is a vector of population least squares coefficients of `X y` on `X_S`: it vanishes
outside `S` and solves the normal equations `∑ t, C s t β t = C s y` for every `s ∈ S`. -/
def IsRegCoeff (C : Matrix V V ℝ) (S : Finset V) (y : V) (β : V → ℝ) : Prop :=
  (∀ v ∉ S, β v = 0) ∧ ∀ s ∈ S, ∑ t, C s t * β t = C s y

/-- The covariance of two linear combinations `a ⬝ X` and `b ⬝ X` of variables with covariance
matrix `C`: `aᵀ C b`. -/
def covComb (C : Matrix V V ℝ) (a b : V → ℝ) : ℝ := a ⬝ᵥ (C *ᵥ b)

/-- The coefficient vector of the residual `X y - ∑ t, β t X t`. -/
def residual (y : V) (β : V → ℝ) : V → ℝ := Pi.single y 1 - β

/-- The principal submatrix `C_SS` of the covariance matrix. -/
abbrev subCov (C : Matrix V V ℝ) (S : Finset V) : Matrix S S ℝ :=
  C.submatrix Subtype.val Subtype.val

/-- The regression coefficients `C_SS⁻¹ C_Sy`, extended by zero outside `S`. Meaningful only when
`C_SS` is invertible (`regCoeff_isRegCoeff`); otherwise Lean's inverse convention gives zero. -/
noncomputable def regCoeff (C : Matrix V V ℝ) (S : Finset V) (y : V) : V → ℝ := fun v =>
  if h : v ∈ S then
    ((subCov C S)⁻¹ *ᵥ fun s : S => C s y) ⟨v, h⟩
  else 0

/-- The partial covariance of `X x` and `X y` given `X_Z`: the covariance of `X x` with the
residual of the regression of `X y` on `X_Z`, that is the Schur complement entry
`C x y - C_xZ C_ZZ⁻¹ C_Zy`. -/
noncomputable def partialCov (C : Matrix V V ℝ) (Z : Finset V) (x y : V) : ℝ :=
  C x y - ∑ t, C x t * regCoeff C Z y t

omit [DecidableEq V] in
/-- A sum against a vector supported on `S` is a sum over `S`. -/
theorem sum_mul_eq_sum_subtype {S : Finset V} {β : V → ℝ} (hβ : ∀ v ∉ S, β v = 0)
    (f : V → ℝ) : ∑ t, f t * β t = ∑ t : S, f t * β t := by
  rw [Finset.sum_coe_sort S (fun t => f t * β t)]
  exact (Finset.sum_subset (Finset.subset_univ S) fun t _ ht => by rw [hβ t ht, mul_zero]).symm

/-! ### Orthogonality and least squares -/

/-- The orthogonality principle: the normal equations say exactly that the residual
`X y - β ⬝ X` is uncorrelated with every regressor `X s`, `s ∈ S`. -/
theorem isRegCoeff_iff_orthogonal (C : Matrix V V ℝ) (S : Finset V) (y : V) (β : V → ℝ) :
    IsRegCoeff C S y β ↔
      (∀ v ∉ S, β v = 0) ∧ ∀ s ∈ S, covComb C (Pi.single s 1) (residual y β) = 0 := by
  have key : ∀ s, covComb C (Pi.single s 1) (residual y β) = C s y - ∑ t, C s t * β t := by
    intro s
    rw [covComb, single_dotProduct, one_mul, residual, Matrix.mulVec_sub,
      Matrix.mulVec_single_one]
    simp [Matrix.mulVec, dotProduct]
  simp only [IsRegCoeff, key]
  exact and_congr_right fun _ => forall₂_congr fun s _ => by rw [sub_eq_zero, eq_comm]

/-- Population least squares: if `C` is positive semidefinite and `β` solves the normal
equations, then the residual variance `Var(X y - β ⬝ X)` is at most `Var(X y - a ⬝ X)` for every
coefficient vector `a` supported on `S`. -/
theorem IsRegCoeff.residual_variance_le {C : Matrix V V ℝ} {S : Finset V} {y : V} {β : V → ℝ}
    (hC : C.PosSemidef) (hβ : IsRegCoeff C S y β) {a : V → ℝ} (ha : ∀ v ∉ S, a v = 0) :
    covComb C (residual y β) (residual y β) ≤ covComb C (residual y a) (residual y a) := by
  set r := residual y β
  set d := β - a
  have hra : residual y a = r + d := by
    simp only [r, d, residual]; abel
  have hd : ∀ v ∉ S, d v = 0 := fun v hv => by simp [d, hβ.1 v hv, ha v hv]
  have hCr : ∀ s ∈ S, (C *ᵥ r) s = 0 := by
    intro s hs
    have := ((isRegCoeff_iff_orthogonal C S y β).1 hβ).2 s hs
    simpa [covComb] using this
  have hdr : d ⬝ᵥ (C *ᵥ r) = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v ∈ S
    · simp [hCr v hv]
    · simp [hd v hv]
  have hsymm : Cᵀ = C := by
    have := hC.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hrd : r ⬝ᵥ (C *ᵥ d) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, dotProduct_comm, hdr]
  have hdd : 0 ≤ d ⬝ᵥ (C *ᵥ d) := by
    simpa using hC.dotProduct_mulVec_nonneg d
  rw [hra]
  simp only [covComb, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  linarith

/-! ### Existence and uniqueness -/

/-- Uniqueness of the regression coefficients when `C_SS` is invertible. -/
theorem IsRegCoeff.unique {C : Matrix V V ℝ} {S : Finset V} {y : V} {β₁ β₂ : V → ℝ}
    (hS : IsUnit (subCov C S)) (h₁ : IsRegCoeff C S y β₁)
    (h₂ : IsRegCoeff C S y β₂) : β₁ = β₂ := by
  set d := β₁ - β₂
  have hd : ∀ v ∉ S, d v = 0 := fun v hv => by simp [d, h₁.1 v hv, h₂.1 v hv]
  have hdS : (subCov C S) *ᵥ (fun s : S => d s) = 0 := by
    ext s
    have e₁ := h₁.2 s s.2
    have e₂ := h₂.2 s s.2
    have : ∑ t, C s t * d t = 0 := by
      simp only [d, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, e₁, e₂, sub_self]
    rw [sum_mul_eq_sum_subtype hd] at this
    simpa [Matrix.mulVec, dotProduct] using this
  have hz := Matrix.mulVec_injective_of_isUnit hS (hdS.trans (Matrix.mulVec_zero _).symm)
  funext v
  have : d v = 0 := by
    by_cases hv : v ∈ S
    · exact congrFun hz ⟨v, hv⟩
    · exact hd v hv
  simpa [d, sub_eq_zero] using this

/-- When `C_SS` is invertible, `regCoeff C S y = C_SS⁻¹ C_Sy` solves the normal equations. -/
theorem regCoeff_isRegCoeff {C : Matrix V V ℝ} {S : Finset V} (y : V)
    (hS : IsUnit (subCov C S)) : IsRegCoeff C S y (regCoeff C S y) := by
  have hsupp : ∀ v ∉ S, regCoeff C S y v = 0 := fun v hv => by simp [regCoeff, hv]
  refine ⟨hsupp, fun s hs => ?_⟩
  rw [sum_mul_eq_sum_subtype hsupp]
  have hinv := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hS)
  have := congrFun (congrArg (fun A => A *ᵥ fun s : S => C s y) hinv) ⟨s, hs⟩
  simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at this
  rw [← this]
  simp [Matrix.mulVec, dotProduct, regCoeff]

/-- When `C_SS` is invertible, `β` solves the normal equations exactly when `β = C_SS⁻¹ C_Sy`. -/
theorem isRegCoeff_iff_eq_regCoeff {C : Matrix V V ℝ} {S : Finset V} {y : V} {β : V → ℝ}
    (hS : IsUnit (subCov C S)) :
    IsRegCoeff C S y β ↔ β = regCoeff C S y :=
  ⟨fun h => h.unique hS (regCoeff_isRegCoeff y hS), fun h => h ▸ regCoeff_isRegCoeff y hS⟩

omit [Fintype V] in
/-- For a positive definite covariance matrix every `C_SS` is invertible. -/
theorem isUnit_submatrix_of_posDef {C : Matrix V V ℝ} (hC : C.PosDef) (S : Finset V) :
    IsUnit (subCov C S) :=
  (hC.submatrix Subtype.coe_injective).isUnit

/-! ### Closed forms for one and two regressors -/

/-- The simple regression slope (Primer equation 1.22): if `C x x ≠ 0`, the regression of `X y` on
`X x` alone has the single coefficient `r_YX = C x y / C x x`. -/
theorem isRegCoeff_singleton_iff {C : Matrix V V ℝ} {x y : V} {β : V → ℝ} (hxx : C x x ≠ 0) :
    IsRegCoeff C {x} y β ↔ β = Pi.single x (C x y / C x x) := by
  have hsum : ∀ γ : V → ℝ, (∀ v ∉ ({x} : Finset V), γ v = 0) →
      ∑ t, C x t * γ t = C x x * γ x := fun γ hγ => by
    rw [Finset.sum_eq_single x (fun b _ hb => by rw [hγ b (by simpa using hb), mul_zero])
      (by simp)]
  constructor
  · rintro ⟨hs, hn⟩
    have h := hn x (by simp)
    rw [hsum β hs] at h
    funext v
    by_cases hv : v = x
    · subst hv; simp only [Pi.single_eq_same]; field_simp; linarith
    · simp [hv, hs v (by simpa using hv)]
  · rintro rfl
    have hs : ∀ v ∉ ({x} : Finset V), (Pi.single x (C x y / C x x) : V → ℝ) v = 0 :=
      fun v hv => by simp [show v ≠ x by simpa using hv]
    refine ⟨hs, fun s hs' => ?_⟩
    rw [Finset.mem_singleton] at hs'
    subst hs'
    rw [hsum _ hs]
    simp only [Pi.single_eq_same]
    field_simp

/-- The simple regression slope `r_YX = C x y / C x x` of `X y` on `X x` (Primer equation 1.22).
It is the regression coefficient when `C x x ≠ 0` (`isRegCoeff_singleton_iff`). -/
noncomputable def regSlope (C : Matrix V V ℝ) (x y : V) : ℝ := C x y / C x x

/-- A sum against a vector supported on `{x, z}`. -/
theorem sum_mul_eq_of_support_pair {x z : V} (hxz : x ≠ z) {β : V → ℝ}
    (hβ : ∀ v ∉ ({x, z} : Finset V), β v = 0) (f : V → ℝ) :
    ∑ t, f t * β t = f x * β x + f z * β z := by
  rw [← Finset.sum_pair hxz (f := fun t => f t * β t)]
  exact (Finset.sum_subset (Finset.subset_univ _) fun t _ ht => by rw [hβ t ht, mul_zero]).symm

/-- The two regressor formulas (Primer equations 1.27 and 1.28): with `D = C x x C z z - C x z ²`
nonzero, the regression of `X y` on `X x` and `X z` has coefficients
`r_YX·Z = (C z z C x y - C x z C z y) / D` and `r_YZ·X = (C x x C z y - C x z C x y) / D`. -/
theorem isRegCoeff_pair_iff {C : Matrix V V ℝ} {x z y : V} {β : V → ℝ} (hxz : x ≠ z)
    (hsymm : C z x = C x z) (hD : C x x * C z z - C x z ^ 2 ≠ 0) :
    IsRegCoeff C {x, z} y β ↔ (∀ v ∉ ({x, z} : Finset V), β v = 0) ∧
      β x = (C z z * C x y - C x z * C z y) / (C x x * C z z - C x z ^ 2) ∧
      β z = (C x x * C z y - C x z * C x y) / (C x x * C z z - C x z ^ 2) := by
  constructor
  · rintro ⟨hs, hn⟩
    have h1 := hn x (by simp)
    have h2 := hn z (by simp)
    rw [sum_mul_eq_of_support_pair hxz hs] at h1 h2
    rw [hsymm] at h2
    refine ⟨hs, ?_, ?_⟩
    · rw [eq_div_iff hD]; linear_combination C z z * h1 - C x z * h2
    · rw [eq_div_iff hD]; linear_combination C x x * h2 - C x z * h1
  · rintro ⟨hs, hx, hz⟩
    refine ⟨hs, fun s hs' => ?_⟩
    rw [sum_mul_eq_of_support_pair hxz hs, hx, hz, mul_div_assoc', mul_div_assoc',
      ← add_div, div_eq_iff hD]
    rcases Finset.mem_insert.1 hs' with rfl | hs'
    · ring
    · rw [Finset.mem_singleton] at hs'
      subst hs'
      rw [hsymm]
      ring

omit [DecidableEq V] in
/-- The regression on one regressor exists when `C x x ≠ 0`. -/
theorem exists_isRegCoeff_singleton {C : Matrix V V ℝ} {x : V} (y : V) (hxx : C x x ≠ 0) :
    ∃ β, IsRegCoeff C {x} y β := by
  classical
  exact ⟨_, (isRegCoeff_singleton_iff hxx).2 rfl⟩

/-- The regression on two regressors exists when `D = C x x C z z - C x z ²` is nonzero. -/
theorem exists_isRegCoeff_pair {C : Matrix V V ℝ} {x z : V} (y : V) (hxz : x ≠ z)
    (hsymm : C z x = C x z) (hD : C x x * C z z - C x z ^ 2 ≠ 0) :
    ∃ β, IsRegCoeff C {x, z} y β := by
  refine ⟨fun v => if v = x then (C z z * C x y - C x z * C z y) / (C x x * C z z - C x z ^ 2)
    else if v = z then (C x x * C z y - C x z * C x y) / (C x x * C z z - C x z ^ 2) else 0,
    (isRegCoeff_pair_iff hxz hsymm hD).2 ⟨fun v hv => ?_, by simp, by simp [Ne.symm hxz]⟩⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  simp [hv.1, hv.2]

/-! ### Vanishing partial regression coefficients and partial covariances -/

/-- A zero partial regression coefficient is a zero partial covariance: for `x ∉ Z`, with `C_ZZ`
and `C_SS` invertible (`S = insert x Z`), the coefficient of `x` in the regression of `y` on `x`
and `Z` is zero if and only if the partial covariance of `x` and `y` given `Z` is zero. -/
theorem IsRegCoeff.eq_zero_iff_partialCov_eq_zero {C : Matrix V V ℝ} {Z : Finset V} {x y : V}
    {β : V → ℝ} (hx : x ∉ Z) (hZ : IsUnit (subCov C Z))
    (hS : IsUnit (subCov C (insert x Z)))
    (hβ : IsRegCoeff C (insert x Z) y β) : β x = 0 ↔ partialCov C Z x y = 0 := by
  have hγ := regCoeff_isRegCoeff y hZ
  constructor
  · intro h0
    have hβZ : IsRegCoeff C Z y β := by
      refine ⟨fun v hv => ?_, fun s hs => hβ.2 s (Finset.mem_insert_of_mem hs)⟩
      by_cases hvx : v = x
      · exact hvx ▸ h0
      · exact hβ.1 v (by simp [hvx, hv])
    have hEq := hβZ.unique hZ hγ
    have := hβ.2 x (Finset.mem_insert_self x Z)
    rw [hEq] at this
    rw [partialCov, this, sub_self]
  · intro h0
    have hγS : IsRegCoeff C (insert x Z) y (regCoeff C Z y) := by
      refine ⟨fun v hv => hγ.1 v fun h => hv (Finset.mem_insert_of_mem h), fun s hs => ?_⟩
      rcases Finset.mem_insert.1 hs with rfl | hs
      · rw [partialCov, sub_eq_zero] at h0; exact h0.symm
      · exact hγ.2 s hs
    rw [hβ.unique hS hγS]
    exact hγ.1 x hx

/-- The explicit form for one covariate: with `C z z ≠ 0` and `D ≠ 0`, the coefficient of `x` in
the regression of `y` on `x` and `z` vanishes if and only if the partial covariance
`C x y - C x z C z y / C z z` vanishes. -/
theorem isRegCoeff_pair_fst_eq_zero_iff {C : Matrix V V ℝ} {x z y : V} {β : V → ℝ}
    (hxz : x ≠ z) (hsymm : C z x = C x z) (hzz : C z z ≠ 0)
    (hD : C x x * C z z - C x z ^ 2 ≠ 0) (hβ : IsRegCoeff C {x, z} y β) :
    β x = 0 ↔ C x y - C x z * C z y / C z z = 0 := by
  rw [((isRegCoeff_pair_iff hxz hsymm hD).1 hβ).2.1, div_eq_zero_iff, or_iff_left hD]
  constructor
  · intro h; field_simp; linarith
  · intro h; field_simp at h; linarith

end CausalInference
