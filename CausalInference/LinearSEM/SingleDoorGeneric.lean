/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.SingleDoorConverse
public import CausalInference.Graphical.GlobalMarkovCompleteness

/-!
# The generic converse of the single-door criterion: the polynomial argument

For an acyclic graph `G` the parameters of a linear SEM on `G` with uncorrelated errors are a
path coefficient for every edge and an error variance for every vertex; `Param G` is the space
of these parameter vectors, `paramB` and `paramCov` give the coefficient matrix and the implied
covariance `T Ω Tᵀ`, and `exceptional x y S` is the set of parameter vectors with positive error
variances at which the coefficient of `x` in the regression of `y` on `S` equals the path
coefficient of `x → y`.

## Main results

* `SingleDoorGeneric.biasPoly`: the numerator `adj(Σ_SS) Σ_Sy - α det(Σ_SS)` of the bias, a
  polynomial in all parameters (`MvPolynomial`); `eval_biasPoly_of_isUnit` shows that it
  evaluates to `det(Σ_SS) (r_yx·S - α)` whenever `Σ_SS` is invertible.
* `SingleDoorGeneric.biasPoly_ne_zero`: one parameter vector (error variances may be zero) with
  invertible `Σ_SS` and a regression coefficient different from the path coefficient makes the
  bias polynomial nonzero.
* `SingleDoorGeneric.volume_exceptional_eq_zero`: in that case the exceptional set is Lebesgue
  null, since it lies in the zero set of the bias polynomial
  (`exceptional_subset_zeroSet`, `volume_zeroSet_eq_zero_of_fintype`);
  `volume_exceptional_eq_zero_of_model` takes the witness as a linear SEM.
* `SingleDoorGeneric.exists_model_ne`: a null exceptional set leaves a model with positive error
  variances at which the two coefficients differ.
* `SingleDoorGeneric.isUnit_subCov_of_gram`, `SingleDoorGeneric.gram_regCoeff`: invertibility
  and regression for Gram matrices, used for witnesses with degenerate errors.

The witness for an arbitrary open path is built in `CausalInference.LinearSEM.SingleDoorTrail`.

Source: J. Pearl (2009), *Causality*, 2nd edition, Section 5.3.1, Theorem 5.3.1.
-/

@[expose] public section

namespace CausalInference

namespace LinearSEM

open Matrix Finset Relation MeasureTheory

namespace SingleDoorGeneric

/-! ### Zero sets of polynomials indexed by a finite type -/

/-- The zero set of a nonzero real polynomial in finitely many variables, indexed by an
arbitrary finite type, is Lebesgue null (`volume_zeroSet_eq_zero` transported along an
enumeration of the variables). -/
theorem volume_zeroSet_eq_zero_of_fintype {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℝ}
    (hp : p ≠ 0) : volume {x : σ → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  classical
  set e := Fintype.equivFin σ
  have hq : MvPolynomial.rename e p ≠ 0 := fun h =>
    hp (MvPolynomial.rename_injective e e.injective (by rw [h, map_zero]))
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e
  have hcomp : ∀ x : σ → ℝ,
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e x) ∘ e = x := by
    intro x
    funext s
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  have hset : {x : σ → ℝ | MvPolynomial.eval x p = 0} =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card σ) => ℝ) e) ⁻¹'
        {y | MvPolynomial.eval y (MvPolynomial.rename e p) = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, MvPolynomial.eval_rename, hcomp]
  rw [hset, hmp.measure_preimage_equiv]
  exact volume_zeroSet_eq_zero hq

/-! ### The parameter space of a graph -/

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : Digraph V) [DecidableRel G.Adj]

/-- The edges `u → v` of `G`, as pairs `(u, v)`. -/
abbrev Edge : Type _ := {p : V × V // G.Adj p.1 p.2}

/-- A parameter vector of a linear SEM on `G` with uncorrelated errors: a path coefficient for
every edge and an error variance for every vertex. -/
abbrev Param : Type _ := Edge G ⊕ V → ℝ

variable {G}

/-- The coefficient matrix of a parameter vector. -/
def paramB (θ : Param G) : Matrix V V ℝ :=
  fun v u => if h : G.Adj u v then θ (Sum.inl ⟨(u, v), h⟩) else 0

/-- The error covariance of a parameter vector: diagonal, with the error variances. -/
def paramΩ (θ : Param G) : Matrix V V ℝ := diagonal fun v => θ (Sum.inr v)

/-- The total effect matrix `∑ k < |V|, B ^ k` of a parameter vector. -/
def paramT (θ : Param G) : Matrix V V ℝ := ∑ k ∈ range (Fintype.card V), paramB θ ^ k

/-- The implied covariance `T Ω Tᵀ` of a parameter vector. -/
def paramCov (θ : Param G) : Matrix V V ℝ := paramT θ * paramΩ θ * (paramT θ)ᵀ

omit [Fintype V] [DecidableEq V] in
theorem paramB_support (θ : Param G) (v u : V) (h : paramB θ v u ≠ 0) : G.Adj u v := by
  simp only [paramB] at h
  split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

/-- The linear SEM on the acyclic graph `G` of a parameter vector with nonnegative error
variances. -/
def paramModel (hG : G.IsAcyclic) (θ : Param G) (hθ : ∀ v, 0 ≤ θ (Sum.inr v)) :
    LinearSEM V where
  G := G
  acyclic := hG
  B := paramB θ
  B_support := paramB_support θ
  Ω := paramΩ θ
  Ω_posSemidef := PosSemidef.diagonal hθ

theorem paramModel_cov (hG : G.IsAcyclic) (θ : Param G) (hθ : ∀ v, 0 ≤ θ (Sum.inr v)) :
    (paramModel hG θ hθ).cov = paramCov θ := rfl

/-- The parameter vectors with positive error variances at which the coefficient of `x` in the
regression of `y` on `S` equals the path coefficient of `x → y`. -/
def exceptional (x y : V) (S : Finset V) : Set (Param G) :=
  {θ | (∀ v, 0 < θ (Sum.inr v)) ∧ regCoeff (paramCov θ) S y x = paramB θ y x}

/-! ### The bias as a polynomial in the parameters -/

/-- The coefficient matrix with indeterminate path coefficients. -/
noncomputable def polyB : Matrix V V (MvPolynomial (Edge G ⊕ V) ℝ) :=
  fun v u => if h : G.Adj u v then MvPolynomial.X (Sum.inl ⟨(u, v), h⟩) else 0

/-- The implied covariance with indeterminate parameters. -/
noncomputable def polyCov : Matrix V V (MvPolynomial (Edge G ⊕ V) ℝ) :=
  (∑ k ∈ range (Fintype.card V), polyB (G := G) ^ k) *
    diagonal (fun v => MvPolynomial.X (Sum.inr v)) *
      (∑ k ∈ range (Fintype.card V), polyB (G := G) ^ k)ᵀ

/-- **The bias polynomial.** The numerator `adj(Σ_SS) Σ_Sy - α det(Σ_SS)` of the bias of the
regression coefficient of `x`, as a polynomial in the path coefficients and error variances; it
equals `det(Σ_SS) (r_yx·S - α)` whenever `Σ_SS` is invertible (`eval_biasPoly_of_isUnit`). -/
noncomputable def biasPoly (x y : V) (S : Finset V) (hx : x ∈ S) :
    MvPolynomial (Edge G ⊕ V) ℝ :=
  (adjugate ((polyCov (G := G)).submatrix (Subtype.val : S → V) Subtype.val) *ᵥ
      fun s : S => polyCov (G := G) s y) ⟨x, hx⟩ -
    polyB y x * det ((polyCov (G := G)).submatrix (Subtype.val : S → V) Subtype.val)

omit [Fintype V] [DecidableEq V] in
theorem map_polyB (θ : Param G) : (polyB (G := G)).map (MvPolynomial.eval θ) = paramB θ := by
  ext v u
  simp only [Matrix.map_apply, polyB, paramB]
  split_ifs <;> simp

theorem map_polyCov (θ : Param G) :
    (polyCov (G := G)).map (MvPolynomial.eval θ) = paramCov θ := by
  have hT : (∑ k ∈ range (Fintype.card V), polyB (G := G) ^ k).map (MvPolynomial.eval θ) =
      paramT θ := by
    rw [← RingHom.mapMatrix_apply, map_sum]
    simp only [map_pow, RingHom.mapMatrix_apply, map_polyB]
    rfl
  have hD : (diagonal (fun v => (MvPolynomial.X (Sum.inr v) :
      MvPolynomial (Edge G ⊕ V) ℝ))).map (MvPolynomial.eval θ) = paramΩ θ := by
    rw [diagonal_map (map_zero _)]
    simp [paramΩ]
  rw [polyCov, ← RingHom.mapMatrix_apply, map_mul, map_mul]
  simp only [RingHom.mapMatrix_apply, hT, hD, transpose_map]
  rfl

theorem eval_biasPoly (x y : V) (S : Finset V) (hx : x ∈ S) (θ : Param G) :
    MvPolynomial.eval θ (biasPoly x y S hx) =
      (adjugate (subCov (paramCov θ) S) *ᵥ fun s : S => paramCov θ s y) ⟨x, hx⟩ -
        paramB θ y x * det (subCov (paramCov θ) S) := by
  have hsub : (MvPolynomial.eval θ).mapMatrix
      ((polyCov (G := G)).submatrix (Subtype.val : S → V) Subtype.val) =
        subCov (paramCov θ) S := by
    rw [RingHom.mapMatrix_apply, ← submatrix_map, map_polyCov]
  have hB : MvPolynomial.eval θ (polyB (G := G) y x) = paramB θ y x := by
    rw [← map_polyB θ]
    rfl
  rw [biasPoly, map_sub, map_mul, RingHom.map_det, hsub, hB, RingHom.map_mulVec,
    ← RingHom.mapMatrix_apply, RingHom.map_adjugate, hsub]
  congr 2
  funext s
  simp only [Function.comp_apply]
  rw [← map_polyCov θ]
  rfl

/-- When `Σ_SS` is invertible, the bias polynomial evaluates to `det(Σ_SS) (r_yx·S - α)`. -/
theorem eval_biasPoly_of_isUnit (x y : V) (S : Finset V) (hx : x ∈ S) (θ : Param G)
    (hu : IsUnit (subCov (paramCov θ) S)) :
    MvPolynomial.eval θ (biasPoly x y S hx) =
      det (subCov (paramCov θ) S) * (regCoeff (paramCov θ) S y x - paramB θ y x) := by
  have hdet : det (subCov (paramCov θ) S) ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  rw [eval_biasPoly]
  simp only [regCoeff, hx, ↓reduceDIte]
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  field_simp

/-! ### A single witness makes the exceptional set null -/

/-- **The bias polynomial is not zero as soon as one parameter vector is not exceptional.** If
at some parameter vector `θ₀` (with arbitrary, possibly zero, error variances) the block `Σ_SS`
is invertible and the regression coefficient of `x` differs from the path coefficient, then the
bias polynomial `biasPoly x y S hx` is not the zero polynomial. -/
theorem biasPoly_ne_zero {x y : V} {S : Finset V} (hx : x ∈ S) {θ₀ : Param G}
    (hu₀ : IsUnit (subCov (paramCov θ₀) S))
    (hne : regCoeff (paramCov θ₀) S y x ≠ paramB θ₀ y x) :
    biasPoly (G := G) x y S hx ≠ 0 := by
  intro h
  have h0 := congrArg (MvPolynomial.eval θ₀) h
  rw [eval_biasPoly_of_isUnit x y S hx θ₀ hu₀, map_zero] at h0
  exact mul_ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 hu₀).ne_zero (sub_ne_zero.2 hne) h0

/-- **The exceptional set lies in the zero set of the bias polynomial.** At a parameter vector
with positive error variances the covariance is positive definite, so `Σ_SS` is invertible and
the bias polynomial vanishes exactly when the regression coefficient equals the path
coefficient. -/
theorem exceptional_subset_zeroSet (hG : G.IsAcyclic) {x y : V} {S : Finset V} (hx : x ∈ S) :
    (exceptional x y S : Set (Param G)) ⊆
      {θ | MvPolynomial.eval θ (biasPoly (G := G) x y S hx) = 0} := by
  intro θ hθ
  obtain ⟨hpos, heq⟩ := hθ
  have hpd : (paramCov θ).PosDef := by
    rw [← paramModel_cov hG θ fun v => (hpos v).le]
    exact cov_posDef _ (posDef_diagonal_iff.2 hpos)
  change MvPolynomial.eval θ (biasPoly x y S hx) = 0
  rw [eval_biasPoly_of_isUnit x y S hx θ (isUnit_submatrix_of_posDef hpd S), heq, sub_self,
    mul_zero]

/-- **The exceptional set is null as soon as one parameter vector is not exceptional.** If at
some parameter vector `θ₀` (with arbitrary, possibly zero, error variances) the block `Σ_SS` is
invertible and the regression coefficient of `x` differs from the path coefficient, then the
parameter vectors with positive error variances at which the regression coefficient equals the
path coefficient form a Lebesgue null set. -/
theorem volume_exceptional_eq_zero (hG : G.IsAcyclic) {x y : V} {S : Finset V} (hx : x ∈ S)
    {θ₀ : Param G} (hu₀ : IsUnit (subCov (paramCov θ₀) S))
    (hne : regCoeff (paramCov θ₀) S y x ≠ paramB θ₀ y x) :
    volume (exceptional x y S : Set (Param G)) = 0 :=
  measure_mono_null (exceptional_subset_zeroSet hG hx)
    (volume_zeroSet_eq_zero_of_fintype (biasPoly_ne_zero hx hu₀ hne))

/-- The parameter vector of a linear SEM whose coefficients are supported on the edges of `G`,
with the diagonal of its error covariance as error variances. -/
def paramOf (M : LinearSEM V) : Param G
  | Sum.inl e => M.B e.1.2 e.1.1
  | Sum.inr v => M.Ω v v

omit [DecidableEq V] in
theorem paramB_paramOf {M : LinearSEM V} (hB : ∀ v u, M.B v u ≠ 0 → G.Adj u v) :
    paramB (paramOf (G := G) M) = M.B := by
  ext v u
  by_cases h : G.Adj u v
  · simp [paramB, paramOf, h]
  · simp only [paramB, h, dite_false]
    exact (not_not.1 fun h' => h (hB v u h')).symm

theorem paramCov_paramOf {M : LinearSEM V} (hB : ∀ v u, M.B v u ≠ 0 → G.Adj u v)
    (hΩ : M.Ω.IsDiag) : paramCov (paramOf (G := G) M) = M.cov := by
  have hΩ' : paramΩ (paramOf (G := G) M) = M.Ω := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [paramΩ, paramOf]
    · rw [paramΩ, diagonal_apply_ne _ hab, hΩ hab]
  rw [paramCov, paramT, paramB_paramOf hB, hΩ']
  rfl

/-- The version of `volume_exceptional_eq_zero` with the witness given as a linear SEM with
uncorrelated errors whose coefficients are supported on the edges of `G`. -/
theorem volume_exceptional_eq_zero_of_model (hG : G.IsAcyclic) {x y : V} {S : Finset V}
    (hx : x ∈ S) (M : LinearSEM V) (hB : ∀ v u, M.B v u ≠ 0 → G.Adj u v) (hΩ : M.Ω.IsDiag)
    (hu : IsUnit (subCov M.cov S)) (hne : regCoeff M.cov S y x ≠ M.B y x) :
    volume (exceptional x y S : Set (Param G)) = 0 := by
  refine volume_exceptional_eq_zero hG hx (θ₀ := paramOf M) ?_ ?_
  · rwa [paramCov_paramOf hB hΩ]
  · rwa [paramCov_paramOf hB hΩ, paramB_paramOf hB]

/-- A null exceptional set leaves a model with positive error variances (so every covariance
block is invertible) at which the regression coefficient differs from the path coefficient. -/
theorem exists_model_ne (hG : G.IsAcyclic) {x y : V} {S : Finset V}
    (h0 : volume (exceptional x y S : Set (Param G)) = 0) :
    ∃ (θ : Param G) (hθ : ∀ v, 0 < θ (Sum.inr v)),
      (paramModel hG θ fun v => (hθ v).le).Ω.PosDef ∧
        regCoeff (paramModel hG θ fun v => (hθ v).le).cov S y x ≠
          (paramModel hG θ fun v => (hθ v).le).B y x := by
  set P : Set (Param G) := {θ | ∀ v, 0 < θ (Sum.inr v)}
  have hP : IsOpen P := by
    have : P = ⋂ v, {θ : Param G | 0 < θ (Sum.inr v)} := by
      ext θ
      simp [P]
    rw [this]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (continuous_apply _)
  have hpos : 0 < volume P := hP.measure_pos volume ⟨fun _ => 1, fun _ => one_pos⟩
  by_contra hcon
  push Not at hcon
  have hsub : P ⊆ exceptional x y S := fun θ hθ => ⟨hθ, hcon θ hθ (posDef_diagonal_iff.2 hθ)⟩
  exact absurd (measure_mono_null hsub h0) hpos.ne'

/-! ### Gram matrices of models with degenerate errors -/

/-- A Gram matrix `C s t = ∑ u, g s u g t u` has an invertible block on `S` when no nontrivial
combination of the rows `g s`, `s ∈ S`, vanishes. -/
theorem isUnit_subCov_of_gram {S : Finset V} {C : Matrix V V ℝ} (g : V → V → ℝ)
    (hC : ∀ a b, C a b = ∑ u, g a u * g b u)
    (hind : ∀ a : V → ℝ, (∀ u, ∑ s ∈ S, a s * g s u = 0) → ∀ s ∈ S, a s = 0) :
    IsUnit (subCov C S) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro p q hpq
  set c : S → ℝ := p - q
  have hc : subCov C S *ᵥ c = 0 := by
    simp only [c, mulVec_sub, hpq, sub_self]
  have hquad : ∑ u, (∑ s : S, c s * g s u) ^ 2 = 0 := by
    have h1 : ∑ s : S, c s * (subCov C S *ᵥ c) s = 0 := by simp [hc]
    rw [← h1]
    simp only [mulVec, dotProduct, submatrix_apply, hC, sq, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
    ring
  have hzero : ∀ u, ∑ s : S, c s * g s u = 0 := fun u => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => sq_nonneg (∑ s : S, c s * g s u))).1
      hquad u (Finset.mem_univ u)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  set a : V → ℝ := fun v => if h : v ∈ S then c ⟨v, h⟩ else 0
  have ha : ∀ u, ∑ s ∈ S, a s * g s u = 0 := fun u => by
    rw [← Finset.sum_coe_sort S]
    simpa [a] using hzero u
  have hc0 : c = 0 := by
    funext s
    have := hind a ha s s.2
    simpa [a] using this
  exact sub_eq_zero.1 hc0

/-- If every vector orthogonal to the rows `g s`, `s ∈ S`, is orthogonal to `g y`, then `g y` is
the combination of the rows `g t` with the regression coefficients of `y` on `S`. -/
theorem gram_regCoeff {S : Finset V} {C : Matrix V V ℝ} (g : V → V → ℝ) {y : V}
    (hC : ∀ a b, C a b = ∑ u, g a u * g b u) (hu : IsUnit (subCov C S))
    (hrel : ∀ n : V → ℝ, (∀ s ∈ S, ∑ u, g s u * n u = 0) → ∑ u, g y u * n u = 0) :
    ∀ u, g y u = ∑ t, regCoeff C S y t * g t u := by
  have hβ := regCoeff_isRegCoeff (C := C) y hu
  set β := regCoeff C S y
  set ρ : V → ℝ := fun u => g y u - ∑ t, β t * g t u
  have horth : ∀ s ∈ S, ∑ u, g s u * ρ u = 0 := by
    intro s hs
    have h := hβ.2 s hs
    simp only [hC] at h
    simp only [ρ, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [← h, Finset.sum_comm]
    refine sub_eq_zero.2 (Finset.sum_congr rfl fun t _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hy := hrel ρ horth
  have hρρ : ∑ u, ρ u ^ 2 = 0 := by
    have e : ∑ u, ρ u ^ 2 = ∑ u, g y u * ρ u - ∑ t, β t * ∑ u, g t u * ρ u := by
      have h1 : ∀ u, ρ u ^ 2 = g y u * ρ u - ∑ t, β t * (g t u * ρ u) := fun u => by
        have hr : ρ u = g y u - ∑ t, β t * g t u := rfl
        calc ρ u ^ 2 = ρ u * ρ u := sq _
          _ = (g y u - ∑ t, β t * g t u) * ρ u := by rw [← hr]
          _ = _ := by
            rw [sub_mul, Finset.sum_mul]
            congr 1
            exact Finset.sum_congr rfl fun t _ => by ring
      rw [Finset.sum_congr rfl fun u _ => h1 u, Finset.sum_sub_distrib,
        Finset.sum_comm (f := fun u t => β t * (g t u * ρ u))]
      congr 1
      exact Finset.sum_congr rfl fun t _ => by rw [Finset.mul_sum]
    rw [e, hy, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t ∈ S
    · rw [horth t ht, mul_zero]
    · rw [hβ.1 t ht, zero_mul]
  intro u
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => sq_nonneg (ρ u))).1 hρρ u
    (Finset.mem_univ u)
  have h0 : ρ u = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  exact sub_eq_zero.1 h0

end SingleDoorGeneric

end LinearSEM

end CausalInference
