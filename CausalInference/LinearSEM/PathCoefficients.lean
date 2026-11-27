/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.Basic
public import CausalInference.LinearSEM.Regression

/-!
# Path coefficients, regression coefficients, and total effects

For a linear SEM `X = B X + ε` with implied covariance `Σ = T Ω Tᵀ`, this file relates structural
coefficients to population regression coefficients computed from `Σ`.

## Main results

* `LinearSEM.isRegCoeff_row_of_uncorrelated`: if the regressor set `S` contains every variable
  with a nonzero coefficient in the equation for `v`, and every regressor is uncorrelated with the
  error `ε v`, then regressing `v` on `S` returns the structural coefficients `B v ·`. Correlated
  errors elsewhere in the model are allowed.
* `LinearSEM.isRegCoeff_of_nondesc`, `LinearSEM.isRegCoeff_parents`: in a Markovian model
  (diagonal `Ω`), regressing `v` on its parents, or on any set of non-descendants of `v` that
  contains its parents, returns the structural coefficients;
  `LinearSEM.regCoeff_parents_eq` states it for the unique regression vector when `Ω` is
  positive definite. With `LinearSEM.direct_effect`, the regression coefficient of a parent is the
  direct effect.
* `LinearSEM.isRegCoeff_insert_total_effect`, `LinearSEM.regCoeff_insert_eq_T`: in a Markovian
  model, the coefficient of `x` in the regression of `y` on `x` and a set `A` of non-descendants of
  `x` containing the parents of `x` is the total effect `T y x`;
  `LinearSEM.regCoeff_parents_total_effect` is the case `A = pa(x)`. Every such `A` satisfies the
  back-door criterion; the general linear back-door theorem (Pearl 2009, Theorem 5.3.2) needs a
  bridge from d-separation to vanishing partial covariance and is not proved here.
* `LinearSEM.cov_instrument`, `LinearSEM.iv_ratio`: if `x` is the only variable in the equation
  for `y`, with coefficient `α`, and `z` is uncorrelated with `ε y`, then `Σ z y = α Σ z x`, so
  `α = Σ z y / Σ z x` when `Σ z x ≠ 0` (the linear instrumental variable formula).

The trek expansion of `Σ` (Wright's path tracing rule) is `LinearSEM.cov_apply` and
`LinearSEM.cov_apply_of_isDiag` in `CausalInference.LinearSEM.Basic`.

Source: J. Pearl (2009), *Causality*, 2nd edition, Section 5.3.1; J. Pearl, M. Glymour and
N. P. Jewell (2016), *Causal Inference in Statistics: A Primer*, Sections 3.8.2 and 3.8.3.
-/

@[expose] public section

namespace CausalInference

namespace LinearSEM

open Matrix Finset Relation

variable {V : Type*} [Fintype V] [DecidableEq V] (M : LinearSEM V)

/-! ### Regressing a variable on its parents -/

/-- Regression on a superset of the parents with exogenous regressors: if every `u` with
`B v u ≠ 0` lies in `S` and every regressor `s ∈ S` is uncorrelated with the error `ε v`
(`(T Ω) s v = 0`), then the structural coefficients `B v ·` solve the normal equations of the
regression of `X v` on `X_S`. -/
theorem isRegCoeff_row_of_uncorrelated (v : V) (S : Finset V)
    (hS : ∀ u, M.B v u ≠ 0 → u ∈ S) (hunc : ∀ s ∈ S, (M.T * M.Ω) s v = 0) :
    IsRegCoeff M.cov S v (M.B v) := by
  refine ⟨fun u hu => not_not.1 fun h => hu (hS u h), fun s hs => ?_⟩
  rw [M.cov_apply_eq s v, hunc s hs, add_zero]
  simp only [mul_comm (M.cov s _)]

/-- In a Markovian model (diagonal `Ω`), regressing `v` on any set `S` of non-descendants of `v`
(`v` itself excluded) that contains all parents of `v` returns the structural coefficients.
This is a Markovian precursor of the single-door criterion (Pearl 2009, Theorem 5.3.1) for all
coefficients of `v` at once; it does not cover correlated errors or regressor sets that omit
some parents. -/
theorem isRegCoeff_of_nondesc (hΩ : M.Ω.IsDiag) (v : V) (S : Finset V)
    (hpa : ∀ u, M.G.Adj u v → u ∈ S) (hnd : ∀ s ∈ S, ¬ ReflTransGen M.G.Adj v s) :
    IsRegCoeff M.cov S v (M.B v) :=
  M.isRegCoeff_row_of_uncorrelated v S (fun u hu => hpa u (M.B_support v u hu))
    fun s hs => by rw [M.T_mul_Ω_apply_of_isDiag hΩ, M.T_apply_eq_zero (hnd s hs), zero_mul]

omit [DecidableEq V] in
/-- A parent of `v` is not reachable from `v`. -/
theorem not_reflTransGen_of_adj {u v : V} (h : M.G.Adj u v) : ¬ ReflTransGen M.G.Adj v u :=
  fun h' => M.acyclic u (TransGen.head' h h')

/-- In a Markovian model, regressing a variable on its parents returns the structural
coefficients (Primer, Section 3.8.3: the structural equation is an identifying regression when
the errors are independent). -/
theorem isRegCoeff_parents [DecidableRel M.G.Adj] (hΩ : M.Ω.IsDiag) (v : V) :
    IsRegCoeff M.cov (M.G.parentsFinset v) v (M.B v) :=
  M.isRegCoeff_of_nondesc hΩ v _ (fun u hu => by simpa using hu)
    fun s hs => M.not_reflTransGen_of_adj (by simpa using hs)

/-- With a diagonal, positive definite error covariance, the population regression coefficients
of `v` on its parents are exactly the path coefficients `B v ·`. -/
theorem regCoeff_parents_eq [DecidableRel M.G.Adj] (hΩ : M.Ω.IsDiag) (hpd : M.Ω.PosDef)
    (v : V) : regCoeff M.cov (M.G.parentsFinset v) v = M.B v :=
  ((M.isRegCoeff_parents hΩ v).unique
    (isUnit_submatrix_of_posDef (M.cov_posDef hpd) _)
    (regCoeff_isRegCoeff v (isUnit_submatrix_of_posDef (M.cov_posDef hpd) _))).symm

/-! ### Total effects by regression -/

/-- In a Markovian model, let `A` be a set of non-descendants of `x` containing the parents of
`x`, and let `γ` be the regression coefficients of `y` on `A`. Then
`γ + T y x (e_x - B x ·)` solves the normal equations of the regression of `y` on `x` and `A`;
its coefficient on `x` is the total effect `T y x`. -/
theorem isRegCoeff_insert_total_effect (hΩ : M.Ω.IsDiag) (x y : V) (A : Finset V)
    (hpa : ∀ u, M.G.Adj u x → u ∈ A) (hA : ∀ a ∈ A, ¬ ReflTransGen M.G.Adj x a)
    {γ : V → ℝ} (hγ : IsRegCoeff M.cov A y γ) :
    IsRegCoeff M.cov (insert x A) y (γ + M.T y x • (Pi.single x 1 - M.B x)) := by
  set τ := M.T y x
  have hxA : x ∉ A := fun h => hA x h ReflTransGen.refl
  have hTA : ∀ a ∈ A, M.T a x = 0 := fun a ha => M.T_apply_eq_zero (hA a ha)
  have hBA : ∀ p, M.B x p ≠ 0 → p ∈ A := fun p hp => hpa p (M.B_support x p hp)
  have hcovA : ∀ a ∈ A, ∑ p, M.B x p * M.cov a p = M.cov a x := fun a ha => by
    rw [M.cov_apply_eq a x, M.T_mul_Ω_apply_of_isDiag hΩ, hTA a ha, zero_mul, add_zero]
  have hxx : ∑ p, M.B x p * M.cov x p = M.cov x x - M.Ω x x := by
    rw [M.cov_apply_eq x x, M.T_mul_Ω_apply_of_isDiag hΩ, M.T_apply_self, one_mul]; ring
  have hyx := M.cov_apply_eq y x
  rw [M.T_mul_Ω_apply_of_isDiag hΩ] at hyx
  -- the sum against the new vector splits into the `γ` part and the `τ` part
  have hβt : ∀ t, (γ + τ • (Pi.single x 1 - M.B x) : V → ℝ) t =
      γ t + τ * ((Pi.single x 1 : V → ℝ) t - M.B x t) := fun t => rfl
  have hsplit : ∀ s, ∑ t, M.cov s t * (γ + τ • (Pi.single x 1 - M.B x) : V → ℝ) t =
      ∑ t, M.cov s t * γ t + τ * (M.cov s x - ∑ p, M.B x p * M.cov s p) := by
    intro s
    have h1 : ∀ t, M.cov s t * (γ + τ • (Pi.single x 1 - M.B x) : V → ℝ) t =
        M.cov s t * γ t + (τ * (M.cov s t * (Pi.single x 1 : V → ℝ) t) -
          τ * (M.B x t * M.cov s t)) := fun t => by rw [hβt]; ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    ring
  refine ⟨fun v hv => ?_, fun s hs => ?_⟩
  · have hvx : v ≠ x := fun h => hv (h ▸ Finset.mem_insert_self x A)
    have hvA : v ∉ A := fun h => hv (Finset.mem_insert_of_mem h)
    have hB : M.B x v = 0 := not_not.1 fun h => hvA (hBA v h)
    simp [hγ.1 v hvA, hvx, hB]
  · rw [hsplit]
    rcases Finset.mem_insert.1 hs with rfl | hs
    · -- the row of `x`
      rw [hxx]
      have hγx : ∑ t, M.cov s t * γ t = ∑ p, M.B s p * M.cov p y := by
        have h1 : ∀ t, M.cov s t * γ t = (∑ p, M.B s p * M.cov t p) * γ t := by
          intro t
          by_cases ht : t ∈ A
          · rw [hcovA t ht, M.cov_symm]
          · rw [hγ.1 t ht, mul_zero, mul_zero]
        simp only [h1, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hp : M.B s p = 0
        · simp [hp]
        · rw [← hγ.2 p (hBA p hp), Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by rw [M.cov_symm t p]; ring
      rw [hγx, M.cov_symm s y, hyx]
      simp only [M.cov_symm y]
      ring
    · -- the rows of `A`
      rw [hcovA s hs, sub_self, mul_zero, add_zero, hγ.2 s hs]

/-- The total effect is a regression coefficient: in a Markovian model with positive definite
error covariance, for every set `A` of non-descendants of `x` containing the parents of `x`, the
coefficient of `x` in the population regression of `y` on `x` and `A` is the total effect
`T y x`. This is a precursor of the linear back-door theorem (Pearl 2009, Theorem 5.3.2): every
such `A` is back-door admissible, but the theorem is stated for this class only, and for
Markovian models only. -/
theorem regCoeff_insert_eq_T (hΩ : M.Ω.IsDiag) (hpd : M.Ω.PosDef) (x y : V) (A : Finset V)
    (hpa : ∀ u, M.G.Adj u x → u ∈ A) (hA : ∀ a ∈ A, ¬ ReflTransGen M.G.Adj x a) :
    regCoeff M.cov (insert x A) y x = M.T y x := by
  have hu := isUnit_submatrix_of_posDef (M.cov_posDef hpd)
  have hγ := regCoeff_isRegCoeff y (hu A)
  have hxA : x ∉ A := fun h => hA x h ReflTransGen.refl
  have hβ := M.isRegCoeff_insert_total_effect hΩ x y A hpa hA hγ
  rw [← hβ.unique (hu _) (regCoeff_isRegCoeff y (hu _))]
  have hBxx : M.B x x = 0 := not_not.1 fun h => M.acyclic.irrefl x (M.B_support x x h)
  simp [hγ.1 x hxA, hBxx]

/-- The case `A = pa(x)`: adjusting for the parents of `x`, the coefficient of `x` in the
population regression of `y` is the total effect `T y x` (Markovian model, positive definite
error covariance). -/
theorem regCoeff_parents_total_effect [DecidableRel M.G.Adj] (hΩ : M.Ω.IsDiag)
    (hpd : M.Ω.PosDef) (x y : V) :
    regCoeff M.cov (insert x (M.G.parentsFinset x)) y x = M.T y x :=
  M.regCoeff_insert_eq_T hΩ hpd x y _ (fun u hu => by simpa using hu)
    fun a ha => M.not_reflTransGen_of_adj (by simpa using ha)

/-! ### Instrumental variables -/

/-- If `x` is the only variable in the equation for `y`, with coefficient `α`, and `z` is
uncorrelated with the error `ε y` (`(T Ω) z y = 0`), then `Σ z y = α Σ z x`. -/
theorem cov_instrument {x y z : V} {α : ℝ} (hB : ∀ p, M.B y p = if p = x then α else 0)
    (hz : (M.T * M.Ω) z y = 0) : M.cov z y = α * M.cov z x := by
  rw [M.cov_apply_eq z y, hz, add_zero]
  simp [hB]

/-- The linear instrumental variable formula (Pearl 2009, Section 3.5, equation (3.46), and
Section 5.3.1): under the hypotheses of `cov_instrument` and the relevance condition
`Σ z x ≠ 0`, the path coefficient is the covariance ratio `α = Σ z y / Σ z x`. -/
theorem iv_ratio {x y z : V} {α : ℝ} (hB : ∀ p, M.B y p = if p = x then α else 0)
    (hz : (M.T * M.Ω) z y = 0) (hzx : M.cov z x ≠ 0) : M.cov z y / M.cov z x = α := by
  rw [M.cov_instrument hB hz, mul_div_assoc, div_self hzx, mul_one]

end LinearSEM

end CausalInference
