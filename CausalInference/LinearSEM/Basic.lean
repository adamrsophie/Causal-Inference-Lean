/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.TopologicalOrder
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Linear structural equation models

A linear structural equation model (linear SEM) on a finite set of variables `V` is the system
`X = B X + ε`, where `B : Matrix V V ℝ` is the matrix of path coefficients (`B v u` is the
coefficient of `X u` in the equation for `X v`), supported on the edges of a directed acyclic
graph `G`, and `ε` is a vector of errors with covariance matrix `Ω`. Off-diagonal entries of `Ω`
are correlated errors (bidirected arcs in a path diagram); a diagonal `Ω` means uncorrelated errors.
Everything here is at the level of second moments: no probability space is needed, and
"uncorrelated" (not "independent") is the property a diagonal `Ω` expresses. Uncorrelated errors
need not be independent (for `U` uniform on `{-1, 0, 1}`, `U` and `U ^ 2 - 2 / 3` are uncorrelated
and dependent), so a diagonal `Ω` is not by itself a Markovian model in the sense of independent
disturbances; it is one for an independent realization of the errors, for example a jointly
Gaussian one. A realization of the errors on a probability space is in
`CausalInference.LinearSEM.InstrumentalVariable`.

The error covariance `Ω` is required to be positive semidefinite (the field
`LinearSEM.Ω_posSemidef`), because every result that reads `LinearSEM.cov` as a covariance matrix
needs it: an indefinite symmetric `Ω`, such as `Ω = [-1]` on one vertex, would give a negative
"variance". Symmetry is derived (`LinearSEM.Ω_symm`). The worked examples therefore take a proof
that their error covariance is positive semidefinite as an argument.

## Main definitions

* `CausalInference.LinearSEM V`: the structure (graph, acyclicity, coefficients supported on the
  edges, error covariance).
* `LinearSEM.T`: the total effect matrix `∑_{k < |V|} B ^ k`.
* `LinearSEM.cov`: the implied covariance matrix `T Ω Tᵀ`.
* `LinearSEM.intervene M x`: the model of the intervention `do(X x = t)`, whose coefficient matrix
  has row `x` set to zero, whose graph has the arrows into `x` removed, and whose error
  covariance has row and column `x` set to zero (the value `t` is a constant offset).

## Main results

* `LinearSEM.B_pow_card`: `B ^ |V| = 0` (from a topological order of `G`).
* `LinearSEM.one_sub_B_mul_T`, `LinearSEM.T_eq_inv`: `T = (1 - B)⁻¹`, the finite Neumann series.
* `LinearSEM.solution_iff`: `x = B x + e` if and only if `x = T e`.
* `LinearSEM.T_apply_ne_zero`: `T v u ≠ 0` only when `u = v` or `u` is an ancestor of `v`;
  `LinearSEM.T_apply_self`: `T v v = 1`.
* `LinearSEM.pow_apply_eq_sum_walks`, `LinearSEM.T_apply_eq_sum_walks`: `(B ^ k) v u` is the sum,
  over walks of length `k` from `u` to `v`, of the product of the coefficients along the walk;
  `LinearSEM.walk_injective_of_walkWeight_ne_zero`: a walk with a nonzero product is a directed
  path of `G`. Together: Wright's rule for total effects, `T v u` is the sum over directed paths
  from `u` to `v` of the products of the path coefficients.
* `LinearSEM.cov_apply`: the trek expansion `Σ v w = ∑ a b, T v a Ω a b T w b`.
* `LinearSEM.intervene_T_apply_col`, `LinearSEM.intervene_value`: under `do(X x = t)` the value of
  `X y` is affine in `t` with slope `T y x`: the total effect is the interventional slope;
  `LinearSEM.intervene_cov_apply_self`: the intervened variable has variance zero.
* `LinearSEM.direct_effect`: for `x ≠ y`, holding every variable other than `y` fixed, the slope
  of `X y` in `X x` is the path coefficient `B y x`.

Source: J. Pearl (2009), *Causality*, 2nd edition, Section 5.3.1; J. Pearl, M. Glymour and
N. P. Jewell (2016), *Causal Inference in Statistics: A Primer*, Section 3.8.2 (path coefficients
as direct effects; total effect as the sum over directed paths of the products of coefficients).
-/

@[expose] public section

namespace CausalInference

open Matrix Finset Relation

/-- A linear structural equation model `X = B X + ε` on a finite set of variables `V`.
`B v u` is the path coefficient of the arrow `u → v`; it may be nonzero only on edges of the
directed acyclic graph `G`. `Ω` is the covariance matrix of the errors `ε`, so it is required to
be positive semidefinite (symmetry follows, `LinearSEM.Ω_symm`). Diagonality (uncorrelated
errors) and positive definiteness are not fields but explicit hypotheses of the theorems that use
them. -/
structure LinearSEM (V : Type*) [Fintype V] where
  /-- The causal graph. -/
  G : Digraph V
  /-- The causal graph is acyclic (the model is recursive). -/
  acyclic : G.IsAcyclic
  /-- The path coefficients: `B v u` is the coefficient of `X u` in the equation for `X v`. -/
  B : Matrix V V ℝ
  /-- Coefficients are supported on the edges of `G`. -/
  B_support : ∀ v u, B v u ≠ 0 → G.Adj u v
  /-- The covariance matrix of the errors. -/
  Ω : Matrix V V ℝ
  /-- The error covariance matrix is positive semidefinite, as every covariance matrix is. -/
  Ω_posSemidef : Ω.PosSemidef

namespace LinearSEM

variable {V : Type*} [Fintype V] [DecidableEq V] (M : LinearSEM V)

omit [DecidableEq V] in
/-- The error covariance matrix is symmetric. -/
theorem Ω_symm : M.Ωᵀ = M.Ω := by
  have h := M.Ω_posSemidef.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-! ### Nilpotency of the coefficient matrix -/

/-- If `(B ^ k) v u ≠ 0` then any labeling increasing along the edges increases by at least `k`
from `u` to `v`. -/
theorem le_of_pow_apply_ne_zero {f : V → ℕ} (hf : ∀ ⦃u v⦄, M.G.Adj u v → f u < f v) :
    ∀ (k : ℕ) {v u : V}, (M.B ^ k) v u ≠ 0 → f u + k ≤ f v := by
  intro k
  induction k with
  | zero =>
    intro v u h
    by_contra hne
    have : u ≠ v := by rintro rfl; omega
    exact h (by simp [this.symm])
  | succ k ih =>
    intro v u h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih (left_ne_zero_of_mul hw)
    have h2 := hf (M.B_support _ _ (right_ne_zero_of_mul hw))
    omega

/-- If `(B ^ k) v u ≠ 0` then `v` is reachable from `u` by a directed path. -/
theorem reflTransGen_of_pow_apply_ne_zero :
    ∀ (k : ℕ) {v u : V}, (M.B ^ k) v u ≠ 0 → ReflTransGen M.G.Adj u v := by
  intro k
  induction k with
  | zero =>
    intro v u h
    by_cases huv : u = v
    · exact huv ▸ ReflTransGen.refl
    · exact absurd (by simp [Ne.symm huv]) h
  | succ k ih =>
    intro v u h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ReflTransGen.head (M.B_support _ _ (right_ne_zero_of_mul hw))
      (ih (left_ne_zero_of_mul hw))

/-- If `(B ^ (k + 1)) v u ≠ 0` then `u` is a strict ancestor of `v`. -/
theorem transGen_of_pow_succ_apply_ne_zero (k : ℕ) {v u : V}
    (h : (M.B ^ (k + 1)) v u ≠ 0) : TransGen M.G.Adj u v := by
  rw [pow_succ, Matrix.mul_apply] at h
  obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact TransGen.head' (M.B_support _ _ (right_ne_zero_of_mul hw))
    (M.reflTransGen_of_pow_apply_ne_zero k (left_ne_zero_of_mul hw))

/-- The coefficient matrix of a linear SEM over an acyclic graph is nilpotent:
`B ^ |V| = 0`. -/
theorem B_pow_card : M.B ^ Fintype.card V = 0 := by
  obtain ⟨e, he⟩ := M.acyclic.exists_equiv_fin_adj_lt
  ext v u
  by_contra h
  have := M.le_of_pow_apply_ne_zero (f := fun w => (e w : ℕ)) (fun _ _ h => he h) _ h
  have := (e v).isLt
  simp only [Matrix.zero_apply] at *
  omega

theorem isNilpotent_B : IsNilpotent M.B := ⟨_, M.B_pow_card⟩

/-! ### The total effect matrix -/

/-- The total effect matrix `T = ∑_{k < |V|} B ^ k`, the finite Neumann series of `(1 - B)⁻¹`.
`T v u` is the total effect of `X u` on `X v`. -/
def T : Matrix V V ℝ := ∑ k ∈ range (Fintype.card V), M.B ^ k

theorem one_sub_B_mul_T : (1 - M.B) * M.T = 1 := by
  rw [T, mul_neg_geom_sum, B_pow_card, sub_zero]

theorem T_mul_one_sub_B : M.T * (1 - M.B) = 1 := by
  rw [T, geom_sum_mul_neg, B_pow_card, sub_zero]

/-- The total effect matrix is the inverse of `1 - B`. -/
theorem T_eq_inv : M.T = (1 - M.B)⁻¹ := (inv_eq_right_inv M.one_sub_B_mul_T).symm

/-- `T = 1 + B T`: each total effect is the direct contribution plus the effects through the
children. -/
theorem T_eq_one_add_B_mul_T : M.T = 1 + M.B * M.T := by
  have := M.one_sub_B_mul_T
  rw [sub_mul, one_mul] at this
  rw [← this]; abel

/-- `T = 1 + T B`. -/
theorem T_eq_one_add_T_mul_B : M.T = 1 + M.T * M.B := by
  have := M.T_mul_one_sub_B
  rw [mul_sub, mul_one] at this
  rw [← this]; abel

/-- Uniqueness of the inverse: any right inverse of `1 - B` is the total effect matrix. This is
the practical way to compute `T` in examples. -/
theorem T_eq_of_mul_eq_one {A : Matrix V V ℝ} (h : (1 - M.B) * A = 1) : M.T = A := by
  calc M.T = M.T * ((1 - M.B) * A) := by rw [h, mul_one]
    _ = A := by rw [← mul_assoc, T_mul_one_sub_B, one_mul]

/-- The structural equations `x = B x + e` have the unique solution `x = T e`. -/
theorem solution_iff (x e : V → ℝ) : x = M.B *ᵥ x + e ↔ x = M.T *ᵥ e := by
  constructor
  · intro h
    have : (1 - M.B) *ᵥ x = e := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      nth_rewrite 1 [h]; abel
    rw [← this, Matrix.mulVec_mulVec, T_mul_one_sub_B, Matrix.one_mulVec]
  · intro h
    rw [h, Matrix.mulVec_mulVec]
    nth_rewrite 1 [M.T_eq_one_add_B_mul_T]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, add_comm]

/-- A nonzero total effect `T v u` requires `u = v` or a directed path from `u` to `v`. -/
theorem T_apply_ne_zero {v u : V} (h : M.T v u ≠ 0) : ReflTransGen M.G.Adj u v := by
  rw [T, Matrix.sum_apply] at h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact M.reflTransGen_of_pow_apply_ne_zero k hk

/-- If `v` is not reachable from `u`, the total effect of `u` on `v` is zero. -/
theorem T_apply_eq_zero {v u : V} (h : ¬ ReflTransGen M.G.Adj u v) : M.T v u = 0 :=
  not_not.1 fun h' => h (M.T_apply_ne_zero h')

/-- The total effect of a variable on itself is one. -/
theorem T_apply_self (v : V) : M.T v v = 1 := by
  have hcard : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  rw [T, Matrix.sum_apply, ← Nat.sub_add_cancel hcard, Finset.sum_range_succ']
  rw [Finset.sum_eq_zero, zero_add, pow_zero, Matrix.one_apply_eq]
  intro k _
  by_contra h
  exact M.acyclic v (M.transGen_of_pow_succ_apply_ne_zero k h)

/-! ### Wright's rule for total effects: sums over directed paths -/

/-- The weight of a walk `p 0 → p 1 → ⋯ → p k`: the product of the path coefficients of its
steps. -/
def walkWeight {k : ℕ} (p : Fin (k + 1) → V) : ℝ := ∏ i : Fin k, M.B (p i.succ) (p i.castSucc)

omit [DecidableEq V] in
theorem walkWeight_cons {k : ℕ} (a : V) (p : Fin (k + 1) → V) :
    M.walkWeight (Fin.cons a p : Fin (k + 2) → V) = M.B (p 0) a * M.walkWeight p := by
  simp only [walkWeight, Fin.prod_univ_succ, Fin.cons_succ, Fin.castSucc_zero, Fin.cons_zero,
    ← Fin.succ_castSucc]

/-- `(B ^ k) v u` is the sum, over all walks `u = p 0 → ⋯ → p k = v` of length `k`, of the product
of the path coefficients along the walk. -/
theorem pow_apply_eq_sum_walks (k : ℕ) (v u : V) :
    (M.B ^ k) v u = ∑ p : Fin (k + 1) → V,
      if p 0 = u ∧ p (Fin.last k) = v then M.walkWeight p else 0 := by
  induction k generalizing u with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
    by_cases h : v = u
    · subst h; simp [walkWeight]
    · rw [pow_zero, Matrix.one_apply_ne h]
      refine (Finset.sum_eq_zero fun a _ => ite_eq_right ?_).symm
      rintro ⟨h1, h2⟩
      exact absurd (h2.symm.trans h1) h
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, Finset.sum_mul]
    rw [Finset.sum_comm, ← (Fin.consEquiv (n := k + 1) fun _ => V).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ,
      walkWeight_cons, ite_mul, zero_mul, ite_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    conv_rhs => rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> ring

omit [DecidableEq V] in
/-- A walk with nonzero weight follows the edges of `G`. -/
theorem adj_of_walkWeight_ne_zero {k : ℕ} {p : Fin (k + 1) → V} (h : M.walkWeight p ≠ 0)
    (i : Fin k) : M.G.Adj (p i.castSucc) (p i.succ) :=
  M.B_support _ _ ((Finset.prod_ne_zero_iff.1 h) i (Finset.mem_univ _))

omit [DecidableEq V] in
/-- A walk with nonzero weight never revisits a vertex: it is a directed path of `G`. -/
theorem walk_injective_of_walkWeight_ne_zero {k : ℕ} {p : Fin (k + 1) → V}
    (h : M.walkWeight p ≠ 0) : Function.Injective p := by
  obtain ⟨f, hf, hlt⟩ := M.acyclic.exists_injective_adj_lt
  have hmono : StrictMono (f ∘ p) :=
    Fin.strictMono_iff_lt_succ.2 fun i => hlt (M.adj_of_walkWeight_ne_zero h i)
  exact fun a b hab => hmono.injective (by simp [Function.comp, hab])

/-- Wright's rule for total effects: `T v u` is the sum, over walks from `u` to `v` of length less
than `|V|`, of the products of the path coefficients along the walk. By
`walk_injective_of_walkWeight_ne_zero` and `adj_of_walkWeight_ne_zero`, only directed paths of `G`
contribute, so this is the sum over directed paths from `u` to `v`. -/
theorem T_apply_eq_sum_walks (v u : V) :
    M.T v u = ∑ k ∈ range (Fintype.card V), ∑ p : Fin (k + 1) → V,
      if p 0 = u ∧ p (Fin.last k) = v then M.walkWeight p else 0 := by
  rw [T, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun k _ => M.pow_apply_eq_sum_walks k v u

/-! ### The implied covariance matrix -/

/-- The covariance matrix implied by the model: `Σ = T Ω Tᵀ`, the covariance of `X = T ε`. -/
def cov : Matrix V V ℝ := M.T * M.Ω * M.Tᵀ

/-- The trek expansion of the implied covariance: `Σ v w = ∑ a b, T v a Ω a b T w b`, a sum over
pairs of directed paths `a → ⋯ → v` and `b → ⋯ → w` joined by the error covariance `Ω a b`
(Wright's path tracing rule, with `T` expanded by `T_apply_eq_sum_walks`). -/
theorem cov_apply (v w : V) :
    M.cov v w = ∑ a, ∑ b, M.T v a * M.Ω a b * M.T w b := by
  simp only [cov, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The trek expansion with uncorrelated errors (diagonal `Ω`):
`Σ v w = ∑ a, T v a Ω a a T w a`, a sum over common sources `a` of a directed
path to `v` and a directed path to `w`. -/
theorem cov_apply_of_isDiag (hΩ : M.Ω.IsDiag) (v w : V) :
    M.cov v w = ∑ a, M.T v a * M.Ω a a * M.T w a := by
  rw [cov_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · intro b _ hb
    rw [hΩ (Ne.symm hb), mul_zero, zero_mul]
  · simp

/-- The implied covariance matrix is symmetric. -/
theorem cov_transpose : M.covᵀ = M.cov := by
  rw [cov, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, M.Ω_symm,
    Matrix.mul_assoc]

theorem cov_symm (v w : V) : M.cov v w = M.cov w v := by
  rw [← Matrix.transpose_apply M.cov w v, cov_transpose]

/-- `Σ (1 - B)ᵀ = T Ω`. Entry `(a, x)` is the covariance of `X a` with the error `ε x`. -/
theorem cov_mul_one_sub_B_transpose : M.cov * (1 - M.B)ᵀ = M.T * M.Ω := by
  rw [cov, Matrix.mul_assoc, ← Matrix.transpose_mul, one_sub_B_mul_T, Matrix.transpose_one,
    Matrix.mul_one]

/-- The structural equation for `x` at the level of covariances:
`Σ a x = ∑ p, B x p Σ a p + Cov(X a, ε x)`, where `Cov(X a, ε x) = (T Ω) a x`. -/
theorem cov_apply_eq (a x : V) :
    M.cov a x = ∑ p, M.B x p * M.cov a p + (M.T * M.Ω) a x := by
  have h := congrFun (congrFun M.cov_mul_one_sub_B_transpose a) x
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one,
    Matrix.sub_apply, Matrix.mul_apply] at h
  simp only [Matrix.transpose_apply] at h
  rw [← h]
  simp only [mul_comm (M.B x _)]
  ring

/-- With a diagonal `Ω`, `Cov(X a, ε x) = T a x Ω x x`. -/
theorem T_mul_Ω_apply_of_isDiag (hΩ : M.Ω.IsDiag) (a x : V) :
    (M.T * M.Ω) a x = M.T a x * M.Ω x x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · intro b _ hb
    rw [hΩ hb, mul_zero]
  · simp

/-- The total effect matrix is invertible, with inverse `1 - B`. -/
theorem isUnit_T : IsUnit M.T :=
  ⟨⟨M.T, 1 - M.B, M.T_mul_one_sub_B, M.one_sub_B_mul_T⟩, rfl⟩

/-- A positive definite error covariance gives a positive definite implied covariance. -/
theorem cov_posDef (hΩ : M.Ω.PosDef) : M.cov.PosDef := by
  have h := hΩ.mul_mul_conjTranspose_same (B := M.T)
    (Matrix.vecMul_injective_iff_isUnit.2 M.isUnit_T)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- A positive semidefinite error covariance gives a positive semidefinite implied covariance. -/
theorem cov_posSemidef (hΩ : M.Ω.PosSemidef) : M.cov.PosSemidef := by
  have h := hΩ.mul_mul_conjTranspose_same M.T
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-! ### Interventions and direct effects -/

/-- The diagonal mask `P_x` that zeros coordinate `x`. -/
def coordMask (x : V) : Matrix V V ℝ := Matrix.diagonal fun i => if i = x then 0 else 1

/-- The model of the intervention `do(X x = t)`: the equation for `x` is removed (row `x` of `B` is
set to zero, and the arrows into `x` are deleted from the graph), and the error of `x` is replaced
by the constant `t`, so the row and column `x` of the error covariance are set to zero: the new
error covariance is `P_x Ω P_xᵀ`, with `P_x` the mask `coordMask x`. The value `t` enters as the
deterministic offset of `x` in the error vector, see `intervene_value`; the intervened variable has
variance zero, see `intervene_cov_apply_self`. -/
def intervene (x : V) : LinearSEM V where
  G := M.G.deleteIncoming {x}
  acyclic := M.acyclic.deleteIncoming
  B := M.B.updateRow x 0
  B_support v u h := by
    rw [Matrix.updateRow_apply] at h
    split_ifs at h with hv
    · exact absurd rfl h
    · exact ⟨M.B_support v u h, hv⟩
  Ω := coordMask x * M.Ω * (coordMask x)ᵀ
  Ω_posSemidef := by
    have h := M.Ω_posSemidef.mul_mul_conjTranspose_same (coordMask x)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The error covariance of the intervened model: entries in row or column `x` are zero, the others
are those of `Ω`. -/
theorem intervene_Ω_apply (x i j : V) :
    (M.intervene x).Ω i j = if i = x ∨ j = x then 0 else M.Ω i j := by
  simp only [intervene, coordMask, Matrix.diagonal_transpose, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  by_cases hi : i = x <;> by_cases hj : j = x <;> simp [hi, hj]

/-- Removing the equation of `x` does not change the total effects of `x`:
`T' y x = T y x` for every `y`. -/
theorem intervene_T_apply_col (x y : V) : (M.intervene x).T y x = M.T y x := by
  set B' := (M.intervene x).B
  have hcol : ∀ w, ((1 - B') * M.T) w x = (1 : Matrix V V ℝ) w x := by
    intro w
    by_cases hw : w = x
    · subst hw
      simp [B', intervene, Matrix.mul_apply, Matrix.one_apply, M.T_apply_self]
    · have h := congrFun (congrFun M.one_sub_B_mul_T w) x
      simp only [Matrix.sub_apply, Matrix.mul_apply] at h ⊢
      simpa [B', intervene, Matrix.updateRow_apply, hw] using h
  have hT := (M.intervene x).T_mul_one_sub_B
  calc (M.intervene x).T y x = ((M.intervene x).T * ((1 - B') * M.T)) y x := by
        rw [Matrix.mul_apply]
        simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
    _ = M.T y x := by rw [← Matrix.mul_assoc, hT, Matrix.one_mul]

/-- In the intervened model the row `x` of the total effect matrix is the row of the identity:
`X x` depends on no error other than its own offset. -/
theorem intervene_T_apply_row (x w : V) : (M.intervene x).T x w = (1 : Matrix V V ℝ) x w := by
  rw [(M.intervene x).T_eq_one_add_B_mul_T, Matrix.add_apply, Matrix.mul_apply]
  simp [intervene]

/-- Under `do(X x = t)` with errors `e`, the system is `X = B' X + e'` where `e'` is `e` with
entry `x` replaced by `t`; its solution is `T' e'`. The intervened variable takes the value `t`. -/
theorem intervene_value_self (x : V) (e : V → ℝ) (t : ℝ) :
    ((M.intervene x).T *ᵥ Function.update e x t) x = t := by
  simp [Matrix.mulVec, dotProduct, intervene_T_apply_row, Matrix.one_apply]

/-- Under `do(X x = t)` the intervened variable is a constant: its row of the implied covariance
matrix vanishes. -/
theorem intervene_cov_apply_left (x w : V) : (M.intervene x).cov x w = 0 := by
  rw [cov_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [intervene_T_apply_row, intervene_Ω_apply, Matrix.one_apply]
  by_cases ha : x = a
  · simp [ha]
  · simp [ha]

/-- Under `do(X x = t)` the intervened variable has variance zero. -/
theorem intervene_cov_apply_self (x : V) : (M.intervene x).cov x x = 0 :=
  M.intervene_cov_apply_left x x

/-- The total effect is the interventional slope: under `do(X x = t)` the value of every variable
`y` is affine in `t` with slope `T y x`. -/
theorem intervene_value (x y : V) (e : V → ℝ) (t : ℝ) :
    ((M.intervene x).T *ᵥ Function.update e x t) y =
      ((M.intervene x).T *ᵥ Function.update e x 0) y + t * M.T y x := by
  have : Function.update e x t = Function.update e x 0 + Pi.single x t := by
    ext w
    by_cases hw : w = x
    · subst hw; simp
    · simp [hw]
  rw [this, Matrix.mulVec_add, Pi.add_apply, ← M.intervene_T_apply_col x y]
  simp [Matrix.mulVec_single, mul_comm]

/-- The structural right-hand side is affine in each argument: raising the input `c x` of the
equation for `y` by one raises `(B c) y + e y` by `B y x`. This is a matrix identity, valid for
every `x` and `y`; its causal reading is `direct_effect`, which needs `x ≠ y`. -/
theorem structural_rhs_update_sub (c e : V → ℝ) (x y : V) (t : ℝ) :
    ((M.B *ᵥ Function.update c x (t + 1)) y + e y) - ((M.B *ᵥ Function.update c x t) y + e y) =
      M.B y x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · simp; ring
  · intro b _ hb; simp [hb]
  · simp

omit [DecidableEq V] in
/-- The coefficient of a variable in its own equation is zero (acyclicity). -/
theorem B_apply_self (v : V) : M.B v v = 0 :=
  not_not.1 fun h => M.acyclic.irrefl v (M.B_support v v h)

/-- The path coefficient is the direct effect (Primer, Section 3.8.2). Let `x ≠ y`. Hold every
variable other than `y` fixed by intervention, at the values `c` except that `X x` is set to `t`
(for `X₀`) or to `t + 1` (for `X₁`), and let `X y` obey its structural equation
`X y = (B X) y + e y` with the same error `e y`. Then `X x` takes the values `t` and `t + 1`, and
raising it by one unit raises `X y` by exactly `B y x`. For `x = y` the first part fails: `X y` is
not held fixed, and `B y y = 0` (`B_apply_self`) is no direct effect. -/
theorem direct_effect {x y : V} (hxy : x ≠ y) (c e : V → ℝ) (t : ℝ) {X₀ X₁ : V → ℝ}
    (h₀ : ∀ v, v ≠ y → X₀ v = Function.update c x t v) (h₀y : X₀ y = (M.B *ᵥ X₀) y + e y)
    (h₁ : ∀ v, v ≠ y → X₁ v = Function.update c x (t + 1) v)
    (h₁y : X₁ y = (M.B *ᵥ X₁) y + e y) :
    X₀ x = t ∧ X₁ x = t + 1 ∧ X₁ y - X₀ y = M.B y x := by
  refine ⟨by rw [h₀ x hxy, Function.update_self], by rw [h₁ x hxy, Function.update_self], ?_⟩
  have key : ∀ (X : V → ℝ) (s : ℝ), (∀ v, v ≠ y → X v = Function.update c x s v) →
      (M.B *ᵥ X) y = (M.B *ᵥ Function.update c x s) y := by
    intro X s hX
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v = y
    · subst hv; rw [M.B_apply_self, zero_mul, zero_mul]
    · rw [hX v hv]
  rw [h₀y, h₁y, key X₀ t h₀, key X₁ (t + 1) h₁]
  exact M.structural_rhs_update_sub c e x y t

end LinearSEM

end CausalInference
