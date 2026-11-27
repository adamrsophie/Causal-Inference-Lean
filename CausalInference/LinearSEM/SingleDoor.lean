/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.PathCoefficients
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NoncommRing

/-!
# Single-door identification: worked examples and counterexamples

The single-door criterion (Pearl 2009, Theorem 5.3.1) says that the path coefficient `α` of
`X → Y` equals the partial regression coefficient `r_YX·Z` whenever `Z` contains no descendant of
`Y` and `Z` d-separates `X` from `Y` in the graph with `X → Y` deleted. The general theorem needs
a bridge from d-separation in a path diagram with bidirected arcs to vanishing partial covariance,
which this library does not have; it is not proved here. What is proved, for any error
covariance, is its algebraic core: Pearl's decomposition `r_YX·S = α + I_YX·S`
(`LinearSEM.isRegCoeff_decomposition`, `LinearSEM.regCoeff_eq_add`), where `I_YX·S` is computed in
the model with the coefficient `α` deleted (`LinearSEM.deleteCoeff`), and its consequence
`LinearSEM.single_door_of_partialCov`: if the partial covariance of `X` and `Y` given `Z`
vanishes in that model, then `α = r_YX·Z`. The Markovian precursors are in
`CausalInference.LinearSEM.PathCoefficients`. This file also checks the books' worked examples, with
symbolic coefficients, by direct covariance algebra: each model is a `LinearSEM` on `Fin n`, its
total effect matrix is computed by `LinearSEM.T_eq_of_mul_eq_one`, and each claimed identity
between a structural coefficient and a regression coefficient is proved from the implied
covariance matrix.

The figures themselves are not in the text extract used for this file; each graph below is
reconstructed from the prose of Pearl (2009), Section 5.3.1, and of the Primer, Section 3.8, and
is stated in the docstring of its model.

## Examples

* `Fig57`: `Z → X → Y`, `Z ↔ Y`: `β = r_YX·Z` and `α = r_XZ`.
* `Fig58`: `Z₂ → X`, `Z₂ → Y`, `X ↔ Z₂`, `X → Z₁ → Y`, `Z₁ ↔ Y`, `X → Y`: the total effect
  `β + α γ = r_YX·Z₂`.
* `Fig59`: `Z → X → Y`, `X ↔ Y`: the instrumental variable formula `α = r_YZ / r_XZ`, while the
  plain slope `r_YX` differs from `α` when `Cov(ε_X, ε_Y) ≠ 0`.
* `Fig510`: `X → W → Y`, `X → Z → Y`, `X ↔ Z`: `α β = r_YX·Z`, `α = r_WX`,
  `β = r_YX·Z / r_WX`, `γ = r_YZ·X`.
* `Fig511`: two instruments `X`, `X'` for two treatments `Z`, `W` of `Y`: `α` and `δ` solve a
  2 by 2 linear system of slopes, identified when its determinant is nonzero.
* `PrimerFig313`: the total effect `d + e c` (Primer, Section 3.8.2), for any error covariance.
* `PrimerFig314`: the total effect `γ δ = r_YX·T` by back-door adjustment.
* `PrimerFig315`: the direct effect `α = r_YX·W` by the regression rule.

Sources: J. Pearl (2009), *Causality*, 2nd edition, Section 5.3.1, Theorem 5.3.1, Figures 5.7
to 5.11; J. Pearl, M. Glymour and N. P. Jewell (2016), *Causal Inference in Statistics: A Primer*,
Sections 3.8.2 and 3.8.3, Figures 3.13 to 3.17.
-/

@[expose] public section

namespace CausalInference

namespace LinearSEM

open Matrix Finset

/-! ### The decomposition `r_YX·S = α + I_YX·S` -/

section Decomposition

open Relation

variable {V : Type*} [Fintype V] [DecidableEq V] (M : LinearSEM V)

/-- The model `M` with the coefficient of `x` in the equation for `y` set to zero: the model of
the diagram `G_α` of Theorem 5.3.1, with the edge `x → y` removed. (The graph field is kept;
the support condition only gets weaker.) -/
def deleteCoeff (y x : V) : LinearSEM V where
  G := M.G
  acyclic := M.acyclic
  B := fun i j => if i = y ∧ j = x then 0 else M.B i j
  B_support v u h := by
    by_cases hh : v = y ∧ u = x
    · simp [hh] at h
    · simp only [hh, ite_false] at h
      exact M.B_support v u h
  Ω := M.Ω
  Ω_symm := M.Ω_symm

theorem deleteCoeff_B_apply (y x i j : V) :
    (M.deleteCoeff y x).B i j = if i = y ∧ j = x then 0 else M.B i j := rfl

/-- Deleting the coefficient of `x → y` does not change the total effects on a variable `s` not
reachable from `y`. -/
theorem T_deleteCoeff_apply {y x s : V} (hs : ¬ ReflTransGen M.G.Adj y s) (a : V) :
    (M.deleteCoeff y x).T s a = M.T s a := by
  have hdiff : M.T - (M.deleteCoeff y x).T =
      M.T * (M.B - (M.deleteCoeff y x).B) * (M.deleteCoeff y x).T := by
    calc M.T - (M.deleteCoeff y x).T
        = M.T * ((1 - (M.deleteCoeff y x).B) * (M.deleteCoeff y x).T) -
            (M.T * (1 - M.B)) * (M.deleteCoeff y x).T := by
          rw [(M.deleteCoeff y x).one_sub_B_mul_T, M.T_mul_one_sub_B, Matrix.mul_one,
            Matrix.one_mul]
      _ = M.T * (M.B - (M.deleteCoeff y x).B) * (M.deleteCoeff y x).T := by noncomm_ring
  have hrow : ∀ j, (M.T * (M.B - (M.deleteCoeff y x).B)) s j = 0 := by
    intro j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i = y
    · subst hi
      rw [M.T_apply_eq_zero hs, zero_mul]
    · simp [deleteCoeff_B_apply, hi]
  have h := congrFun (congrFun hdiff s) a
  rw [Matrix.sub_apply, Matrix.mul_apply] at h
  simp only [hrow, zero_mul, Finset.sum_const_zero] at h
  linarith

/-- Covariances among variables not reachable from `y` are unchanged by deleting `x → y`. -/
theorem cov_deleteCoeff {y x s t : V} (hs : ¬ ReflTransGen M.G.Adj y s)
    (ht : ¬ ReflTransGen M.G.Adj y t) : (M.deleteCoeff y x).cov s t = M.cov s t := by
  rw [cov_apply, cov_apply]
  simp only [M.T_deleteCoeff_apply hs, M.T_deleteCoeff_apply ht]
  rfl

/-- The covariance of `y` with a variable `s` not reachable from `y` splits as the covariance in
the model without `x → y` plus `B y x Σ s x`. -/
theorem cov_eq_cov_deleteCoeff_add {y x s : V} (hs : ¬ ReflTransGen M.G.Adj y s) :
    M.cov s y = (M.deleteCoeff y x).cov s y + M.B y x * M.cov s x := by
  rw [M.cov_apply_eq s y, (M.deleteCoeff y x).cov_apply_eq s y]
  have hTΩ : ((M.deleteCoeff y x).T * (M.deleteCoeff y x).Ω) s y = (M.T * M.Ω) s y := by
    simp only [Matrix.mul_apply, M.T_deleteCoeff_apply hs]
    rfl
  rw [hTΩ, ← Finset.sum_erase_add _ _ (Finset.mem_univ x),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
  have hsum : ∑ p ∈ Finset.univ.erase x, M.B y p * M.cov s p =
      ∑ p ∈ Finset.univ.erase x, (M.deleteCoeff y x).B y p * (M.deleteCoeff y x).cov s p := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpx : p ≠ x := Finset.ne_of_mem_erase hp
    simp only [deleteCoeff_B_apply, hpx, and_false, ite_false]
    by_cases hB : M.B y p = 0
    · rw [hB, zero_mul, zero_mul]
    · rw [M.cov_deleteCoeff hs (M.not_reflTransGen_of_adj (M.B_support y p hB))]
  rw [hsum]
  simp only [deleteCoeff_B_apply, and_self, ite_true]
  ring

/-- Pearl's decomposition `r_YX·S = α + I_YX·S` (Pearl 2009, Section 5.3.1): let `x ∈ S` and let
no variable of `S` be reachable from `y` (in particular `S` contains no descendant of `y`). If
`γ` are the regression coefficients of `y` on `S` in the model with the coefficient `α = B y x`
deleted, then `γ + α e_x` are the regression coefficients of `y` on `S` in the model itself. The
correction `γ` does not depend on `α`. Any error covariance is allowed. -/
theorem isRegCoeff_decomposition {x y : V} {S : Finset V} (hx : x ∈ S)
    (hS : ∀ s ∈ S, ¬ ReflTransGen M.G.Adj y s) {γ : V → ℝ}
    (hγ : IsRegCoeff (M.deleteCoeff y x).cov S y γ) :
    IsRegCoeff M.cov S y (γ + M.B y x • Pi.single x 1) := by
  refine ⟨fun v hv => ?_, fun s hs => ?_⟩
  · have hvx : v ≠ x := fun h => hv (h ▸ hx)
    simp [hγ.1 v hv, hvx]
  · have h1 : ∀ t, M.cov s t * (γ + M.B y x • Pi.single x 1 : V → ℝ) t =
        (M.deleteCoeff y x).cov s t * γ t +
          M.B y x * (M.cov s t * (Pi.single x 1 : V → ℝ) t) := by
      intro t
      by_cases ht : t ∈ S
      · rw [M.cov_deleteCoeff (hS s hs) (hS t ht)]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      · have htx : t ≠ x := fun h => ht (h ▸ hx)
        simp [hγ.1 t ht, htx]
    simp only [h1, Finset.sum_add_distrib, hγ.2 s hs, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [M.cov_eq_cov_deleteCoeff_add (hS s hs)]

/-- On a regressor set with no variable reachable from `y`, the principal submatrices of the two
covariance matrices agree. -/
theorem subCov_deleteCoeff {x y : V} {S : Finset V} (hS : ∀ s ∈ S, ¬ ReflTransGen M.G.Adj y s) :
    subCov (M.deleteCoeff y x).cov S = subCov M.cov S := by
  ext s t
  exact M.cov_deleteCoeff (hS s s.2) (hS t t.2)

/-- The decomposition for the unique regression vectors: when `Σ_SS` is invertible,
`r_YX·S = α + I_YX·S`, where `I_YX·S` is the coefficient of `x` in the model with `α = B y x`
deleted. -/
theorem regCoeff_eq_add {x y : V} {S : Finset V} (hx : x ∈ S)
    (hS : ∀ s ∈ S, ¬ ReflTransGen M.G.Adj y s) (hu : IsUnit (subCov M.cov S)) :
    regCoeff M.cov S y x = M.B y x + regCoeff (M.deleteCoeff y x).cov S y x := by
  have hu' : IsUnit (subCov (M.deleteCoeff y x).cov S) := by
    rwa [M.subCov_deleteCoeff hS]
  have h := M.isRegCoeff_decomposition hx hS (regCoeff_isRegCoeff y hu')
  rw [← h.unique hu (regCoeff_isRegCoeff y hu)]
  simp [add_comm]

/-- A precursor of the single-door criterion (Pearl 2009, Theorem 5.3.1), with the graphical
condition replaced by its algebraic content: let `x ∉ Z`, let no variable of `insert x Z` be
reachable from `y`, and suppose that in the model with `α = B y x` deleted the partial covariance
of `x` and `y` given `Z` vanishes (which d-separation of `x` and `y` by `Z` in `G_α` implies in a
linear model; that implication is not proved here). Then `α` is the coefficient of `x` in the
regression of `y` on `x` and `Z`. Any error covariance is allowed. -/
theorem single_door_of_partialCov {x y : V} {Z : Finset V} (hxZ : x ∉ Z)
    (hS : ∀ s ∈ insert x Z, ¬ ReflTransGen M.G.Adj y s)
    (huZ : IsUnit (subCov M.cov Z)) (hu : IsUnit (subCov M.cov (insert x Z)))
    (h0 : partialCov (M.deleteCoeff y x).cov Z x y = 0) :
    regCoeff M.cov (insert x Z) y x = M.B y x := by
  have hSZ : ∀ s ∈ Z, ¬ ReflTransGen M.G.Adj y s := fun s hs => hS s (Finset.mem_insert_of_mem hs)
  have huZ' : IsUnit (subCov (M.deleteCoeff y x).cov Z) := by rwa [M.subCov_deleteCoeff hSZ]
  have hu' : IsUnit (subCov (M.deleteCoeff y x).cov (insert x Z)) := by
    rwa [M.subCov_deleteCoeff hS]
  have hzero := ((regCoeff_isRegCoeff y hu').eq_zero_iff_partialCov_eq_zero hxZ huZ' hu').2 h0
  rw [M.regCoeff_eq_add (Finset.mem_insert_self x Z) hS hu, hzero, add_zero]

end Decomposition

/-! ### Figure 5.7 -/

namespace Fig57

/-- The graph `Z → X → Y` with `Z = 0`, `X = 1`, `Y = 2`. -/
def G : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Figure 5.7 of Pearl (2009): `X = α Z + ε_X`, `Y = β X + ε_Y`, with
`Cov(ε_Z, ε_Y) = ω_ZY` (the bidirected arc `Z ↔ Y`). -/
def model (α β ωz ωx ωy ωzy : ℝ) : LinearSEM (Fin 3) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0; α, 0, 0; 0, β, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := !![ωz, 0, ωzy; 0, ωx, 0; ωzy, 0, ωy]
  Ω_symm := by ext i j; fin_cases i <;> fin_cases j <;> rfl

variable (α β ωz ωx ωy ωzy : ℝ)

theorem T_eq : (model α β ωz ωx ωy ωzy).T = !![1, 0, 0; α, 1, 0; α * β, β, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_three]
    ring

theorem cov_eq (i j : Fin 3) : (model α β ωz ωx ωy ωzy).cov i j =
    ∑ a, ∑ b, (!![1, 0, 0; α, 1, 0; α * β, β, 1] : Matrix (Fin 3) (Fin 3) ℝ) i a *
      (!![ωz, 0, ωzy; 0, ωx, 0; ωzy, 0, ωy] : Matrix (Fin 3) (Fin 3) ℝ) a b *
      (!![1, 0, 0; α, 1, 0; α * β, β, 1] : Matrix (Fin 3) (Fin 3) ℝ) j b := by
  rw [cov_apply, T_eq]; rfl

theorem det_XZ : (model α β ωz ωx ωy ωzy).cov 1 1 * (model α β ωz ωx ωy ωzy).cov 0 0 -
    (model α β ωz ωx ωy ωzy).cov 1 0 ^ 2 = ωx * ωz := by
  simp [cov_eq, Fin.sum_univ_three]; ring

/-- Figure 5.7, single door for `β`: `Z` d-separates `X` and `Y` once `X → Y` is deleted, and the
coefficient of `X` in the regression of `Y` on `X` and `Z` is `β = r_YX·Z`. -/
theorem regression_X_eq (hωx : ωx ≠ 0) (hωz : ωz ≠ 0) {r : Fin 3 → ℝ}
    (hr : IsRegCoeff (model α β ωz ωx ωy ωzy).cov {1, 0} 2 r) : r 1 = β := by
  have hD := (det_XZ α β ωz ωx ωy ωzy).symm ▸ mul_ne_zero hωx hωz
  rw [((isRegCoeff_pair_iff (by decide) ((model α β ωz ωx ωy ωzy).cov_symm 0 1) hD).1 hr).2.1,
    det_XZ, div_eq_iff (mul_ne_zero hωx hωz)]
  simp [cov_eq, Fin.sum_univ_three]
  ring

/-- Figure 5.7, single door for `α`: `Z` and `X` are d-separated by the empty set once `Z → X` is
deleted, and `α = r_XZ`. -/
theorem slope_ZX (hωz : ωz ≠ 0) : regSlope (model α β ωz ωx ωy ωzy).cov 0 1 = α := by
  rw [regSlope, div_eq_iff (by simpa [cov_eq, Fin.sum_univ_three] using hωz)]
  simp [cov_eq, Fin.sum_univ_three]
  ring

end Fig57

/-! ### Figure 5.8 -/

namespace Fig58

/-- The graph with `Z₂ = 0`, `X = 1`, `Z₁ = 2`, `Y = 3` and edges `Z₂ → X`, `Z₂ → Y`, `X → Z₁`,
`X → Y`, `Z₁ → Y`. -/
def G : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨
    (i = 2 ∧ j = 3)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Figure 5.8 of Pearl (2009): `X = a Z₂ + ε_X`, `Z₁ = α X + ε_Z₁`,
`Y = b Z₂ + β X + γ Z₁ + ε_Y`, with bidirected arcs `X ↔ Z₂` (`ω_XZ`) and `Z₁ ↔ Y` (`ω_ZY`). -/
def model (a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy : ℝ) : LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; a, 0, 0, 0; 0, α, 0, 0; b, β, γ, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := !![ω0, ωxz, 0, 0; ωxz, ω1, 0, 0; 0, 0, ω2, ωzy; 0, 0, ωzy, ω3]
  Ω_symm := by ext i j; fin_cases i <;> fin_cases j <;> rfl

variable (a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy : ℝ)

/-- The total effect matrix; entry `(Y, X)` is `β + α γ`. -/
theorem T_eq : (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy).T =
    !![1, 0, 0, 0; a, 1, 0, 0; α * a, α, 1, 0; b + a * (β + α * γ), β + α * γ, γ, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]
    all_goals ring

theorem cov_eq (i j : Fin 4) : (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy).cov i j =
    ∑ k, ∑ l, (!![1, 0, 0, 0; a, 1, 0, 0; α * a, α, 1, 0; b + a * (β + α * γ), β + α * γ, γ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) i k *
      (!![ω0, ωxz, 0, 0; ωxz, ω1, 0, 0; 0, 0, ω2, ωzy; 0, 0, ωzy, ω3] :
        Matrix (Fin 4) (Fin 4) ℝ) k l *
      (!![1, 0, 0, 0; a, 1, 0, 0; α * a, α, 1, 0; b + a * (β + α * γ), β + α * γ, γ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) j l := by
  rw [cov_apply, T_eq]; rfl

theorem det_XZ2 : (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy).cov 1 1 *
    (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy).cov 0 0 -
    (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy).cov 1 0 ^ 2 = ω0 * ω1 - ωxz ^ 2 := by
  simp [cov_eq, Fin.sum_univ_four]; ring

/-- Figure 5.8, back door for the total effect: `Z₂` blocks the back-door paths `X ← Z₂ → Y`
and `X ↔ Z₂ → Y`, and the coefficient of `X` in the regression of `Y` on `X` and `Z₂` is the
total effect `β + α γ = r_YX·Z₂`, although `β` itself is not identified by single door. The
hypothesis `ω0 ω1 ≠ ω_XZ ²` says the errors of `Z₂` and `X` are not perfectly correlated. -/
theorem regression_X_eq (hD : ω0 * ω1 - ωxz ^ 2 ≠ 0) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy).cov {1, 0} 3 r) :
    r 1 = β + α * γ := by
  have hD' := (det_XZ2 a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy).symm ▸ hD
  rw [((isRegCoeff_pair_iff (by decide) ((model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy).cov_symm 0 1)
    hD').1 hr).2.1, det_XZ2, div_eq_iff hD]
  simp [cov_eq, Fin.sum_univ_four]
  ring

end Fig58

/-! ### Figure 5.9 -/

namespace Fig59

/-- The graph `Z → X → Y` with `Z = 0`, `X = 1`, `Y = 2`. -/
def G : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Figure 5.9 of Pearl (2009) (and Figure 3.17 of the Primer): `X = β Z + ε_X`,
`Y = α X + ε_Y`, with `Cov(ε_X, ε_Y) = ω_XY` (the bidirected arc `X ↔ Y`); `Z` is an
instrument. -/
def model (α β ωz ωx ωy ωxy : ℝ) : LinearSEM (Fin 3) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0; β, 0, 0; 0, α, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := !![ωz, 0, 0; 0, ωx, ωxy; 0, ωxy, ωy]
  Ω_symm := by ext i j; fin_cases i <;> fin_cases j <;> rfl

variable (α β ωz ωx ωy ωxy : ℝ)

theorem T_eq : (model α β ωz ωx ωy ωxy).T = !![1, 0, 0; β, 1, 0; α * β, α, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_three]

theorem cov_eq (i j : Fin 3) : (model α β ωz ωx ωy ωxy).cov i j =
    ∑ a, ∑ b, (!![1, 0, 0; β, 1, 0; α * β, α, 1] : Matrix (Fin 3) (Fin 3) ℝ) i a *
      (!![ωz, 0, 0; 0, ωx, ωxy; 0, ωxy, ωy] : Matrix (Fin 3) (Fin 3) ℝ) a b *
      (!![1, 0, 0; β, 1, 0; α * β, α, 1] : Matrix (Fin 3) (Fin 3) ℝ) j b := by
  rw [cov_apply, T_eq]; rfl

/-- The instrumental variable formula (Pearl 2009, Figure 5.9 and equation (3.46)): the ratio of
the slopes of `Y` and of `X` on the instrument `Z` is the path coefficient,
`α = r_YZ / r_XZ`. -/
theorem iv_formula (hβ : β ≠ 0) (hωz : ωz ≠ 0) :
    regSlope (model α β ωz ωx ωy ωxy).cov 0 2 / regSlope (model α β ωz ωx ωy ωxy).cov 0 1 =
      α := by
  simp [regSlope, cov_eq, Fin.sum_univ_three]
  field_simp

/-- The same identity through the general theorem `LinearSEM.iv_ratio`. -/
theorem iv_formula' (hβ : β ≠ 0) (hωz : ωz ≠ 0) :
    (model α β ωz ωx ωy ωxy).cov 0 2 / (model α β ωz ωx ωy ωxy).cov 0 1 = α := by
  refine (model α β ωz ωx ωy ωxy).iv_ratio (x := 1) (fun p => ?_) ?_ ?_
  · fin_cases p <;> simp [model]
  · rw [Matrix.mul_apply, T_eq]; simp [model, Fin.sum_univ_three]
  · simp [cov_eq, Fin.sum_univ_three, hβ, hωz]

/-- Without the instrument, the slope `r_YX` is biased by the confounding arc:
`r_YX = α + ω_XY / Var(X)` with `Var(X) = β ² ω_Z + ω_X`. -/
theorem slope_XY (hx : β ^ 2 * ωz + ωx ≠ 0) :
    regSlope (model α β ωz ωx ωy ωxy).cov 1 2 = α + ωxy / (β ^ 2 * ωz + ωx) := by
  have h11 : (model α β ωz ωx ωy ωxy).cov 1 1 = β ^ 2 * ωz + ωx := by
    simp [cov_eq, Fin.sum_univ_three]; ring
  have h12 : (model α β ωz ωx ωy ωxy).cov 1 2 = α * (β ^ 2 * ωz + ωx) + ωxy := by
    simp [cov_eq, Fin.sum_univ_three]; ring
  rw [regSlope, h11, h12]
  field_simp

end Fig59

/-! ### Figure 5.10 -/

namespace Fig510

/-- The graph with `X = 0`, `W = 1`, `Z = 2`, `Y = 3` and edges `X → W`, `W → Y`, `X → Z`,
`Z → Y`. -/
def G : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 3) ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 3)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Figure 5.10 of Pearl (2009): `W = α X + ε_W`, `Z = δ X + ε_Z`, `Y = β W + γ Z + ε_Y`, with the
bidirected arc `X ↔ Z` (`ω_XZ`). The total effect `α β + γ δ` of `X` on `Y` is not identified by
the back-door criterion. -/
def model (α β γ δ ω0 ω1 ω2 ω3 ωxz : ℝ) : LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; α, 0, 0, 0; δ, 0, 0, 0; 0, β, γ, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := !![ω0, 0, ωxz, 0; 0, ω1, 0, 0; ωxz, 0, ω2, 0; 0, 0, 0, ω3]
  Ω_symm := by ext i j; fin_cases i <;> fin_cases j <;> rfl

variable (α β γ δ ω0 ω1 ω2 ω3 ωxz : ℝ)

/-- The total effect matrix; entry `(Y, X)` is `α β + γ δ`. -/
theorem T_eq : (model α β γ δ ω0 ω1 ω2 ω3 ωxz).T =
    !![1, 0, 0, 0; α, 1, 0, 0; δ, 0, 1, 0; α * β + γ * δ, β, γ, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]
    ring

theorem cov_eq (i j : Fin 4) : (model α β γ δ ω0 ω1 ω2 ω3 ωxz).cov i j =
    ∑ k, ∑ l, (!![1, 0, 0, 0; α, 1, 0, 0; δ, 0, 1, 0; α * β + γ * δ, β, γ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) i k *
      (!![ω0, 0, ωxz, 0; 0, ω1, 0, 0; ωxz, 0, ω2, 0; 0, 0, 0, ω3] :
        Matrix (Fin 4) (Fin 4) ℝ) k l *
      (!![1, 0, 0, 0; α, 1, 0, 0; δ, 0, 1, 0; α * β + γ * δ, β, γ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) j l := by
  rw [cov_apply, T_eq]; rfl

theorem det_XZ : (model α β γ δ ω0 ω1 ω2 ω3 ωxz).cov 0 0 *
    (model α β γ δ ω0 ω1 ω2 ω3 ωxz).cov 2 2 -
    (model α β γ δ ω0 ω1 ω2 ω3 ωxz).cov 0 2 ^ 2 = ω0 * ω2 - ωxz ^ 2 := by
  simp [cov_eq, Fin.sum_univ_four]; ring

/-- Figure 5.10: conditioning on `Z` blocks every path through `Z`, so the coefficient of `X` in
the regression of `Y` on `X` and `Z` is the effect `α β` mediated by `W`, and conditioning on `X`
blocks the back-door paths from `Z`, so the coefficient of `Z` is `γ = r_YZ·X`. -/
theorem regression_eq (hD : ω0 * ω2 - ωxz ^ 2 ≠ 0) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α β γ δ ω0 ω1 ω2 ω3 ωxz).cov {0, 2} 3 r) :
    r 0 = α * β ∧ r 2 = γ := by
  have hD' := (det_XZ α β γ δ ω0 ω1 ω2 ω3 ωxz).symm ▸ hD
  obtain ⟨-, h0, h2⟩ := (isRegCoeff_pair_iff (by decide)
    ((model α β γ δ ω0 ω1 ω2 ω3 ωxz).cov_symm 2 0) hD').1 hr
  rw [det_XZ] at h0 h2
  rw [h0, h2, div_eq_iff hD, div_eq_iff hD]
  constructor
  · simp [cov_eq, Fin.sum_univ_four]; ring
  · simp [cov_eq, Fin.sum_univ_four]; ring

/-- Figure 5.10: there is no back-door path from `X` to `W`, so `α = r_WX`. -/
theorem slope_XW (hω0 : ω0 ≠ 0) : regSlope (model α β γ δ ω0 ω1 ω2 ω3 ωxz).cov 0 1 = α := by
  rw [regSlope, div_eq_iff (by simpa [cov_eq, Fin.sum_univ_four] using hω0)]
  simp [cov_eq, Fin.sum_univ_four]
  ring

/-- Figure 5.10: `β = r_YX·Z / r_WX`. -/
theorem beta_eq (hD : ω0 * ω2 - ωxz ^ 2 ≠ 0) (hω0 : ω0 ≠ 0) (hα : α ≠ 0) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α β γ δ ω0 ω1 ω2 ω3 ωxz).cov {0, 2} 3 r) :
    r 0 / regSlope (model α β γ δ ω0 ω1 ω2 ω3 ωxz).cov 0 1 = β := by
  rw [(regression_eq α β γ δ ω0 ω1 ω2 ω3 ωxz hD hr).1, slope_XW α β γ δ ω0 ω1 ω2 ω3 ωxz hω0]
  field_simp

end Fig510

/-! ### Figure 5.11 -/

namespace Fig511

/-- The graph with instruments `X = 0`, `X' = 1`, treatments `Z = 2`, `W = 3`, outcome `Y = 4`,
and edges from each instrument to each treatment and from each treatment to `Y`. -/
def G : Digraph (Fin 5) where
  Adj i j := (i.val < 2 ∧ (j = 2 ∨ j = 3)) ∨ ((i = 2 ∨ i = 3) ∧ j = 4)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Figure 5.11 of Pearl (2009): `Z = b X + c X' + ε_Z`, `W = b' X + c' X' + ε_W`,
`Y = α Z + δ W + ε_Y`, with the errors of `Z`, `W`, `Y` arbitrarily correlated and the
instruments `X`, `X'` uncorrelated with everything else. -/
def model (b c b' c' α δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34 : ℝ) : LinearSEM (Fin 5) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; b, c, 0, 0, 0; b', c', 0, 0, 0; 0, 0, α, δ, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := !![ω0, 0, 0, 0, 0; 0, ω1, 0, 0, 0; 0, 0, ω2, ω23, ω24; 0, 0, ω23, ω3, ω34;
    0, 0, ω24, ω34, ω4]
  Ω_symm := by ext i j; fin_cases i <;> fin_cases j <;> rfl

variable (b c b' c' α δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34 : ℝ)

theorem T_eq : (model b c b' c' α δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34).T =
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; b, c, 1, 0, 0; b', c', 0, 1, 0;
      α * b + δ * b', α * c + δ * c', α, δ, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_five]
    all_goals ring

/-- The covariances of the instruments with the other variables. -/
theorem cov_instruments :
    let C := (model b c b' c' α δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34).cov
    C 0 0 = ω0 ∧ C 1 1 = ω1 ∧ C 0 2 = b * ω0 ∧ C 1 2 = c * ω1 ∧ C 0 3 = b' * ω0 ∧
      C 1 3 = c' * ω1 ∧ C 0 4 = (α * b + δ * b') * ω0 ∧ C 1 4 = (α * c + δ * c') * ω1 := by
  simp only [cov_apply, T_eq, Fin.sum_univ_five]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [model] <;> ring

/-- Figure 5.11: no single pair identifies `α` or `δ`, but the four instrument slopes
`r_ZX = b`, `r_ZX' = c`, `r_WX = b'`, `r_WX' = c'` and the two slopes `r_YX = α b + δ b'`,
`r_YX' = α c + δ c'` give two linear equations in `α` and `δ`, solvable when the determinant
`b c' - b' c` is nonzero: `α = (r_WX' r_YX - r_WX r_YX') / (r_ZX r_WX' - r_WX r_ZX')` and
`δ = (r_ZX r_YX' - r_ZX' r_YX) / (r_ZX r_WX' - r_WX r_ZX')`. -/
theorem identify (hω0 : ω0 ≠ 0) (hω1 : ω1 ≠ 0) (hdet : b * c' - b' * c ≠ 0) :
    let C := (model b c b' c' α δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34).cov
    (regSlope C 1 3 * regSlope C 0 4 - regSlope C 0 3 * regSlope C 1 4) /
        (regSlope C 0 2 * regSlope C 1 3 - regSlope C 0 3 * regSlope C 1 2) = α ∧
      (regSlope C 0 2 * regSlope C 1 4 - regSlope C 1 2 * regSlope C 0 4) /
        (regSlope C 0 2 * regSlope C 1 3 - regSlope C 0 3 * regSlope C 1 2) = δ := by
  obtain ⟨h00, h11, h02, h12, h03, h13, h04, h14⟩ :=
    cov_instruments b c b' c' α δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34
  simp only [regSlope, h00, h11, h02, h12, h03, h13, h04, h14, mul_div_cancel_right₀ _ hω0,
    mul_div_cancel_right₀ _ hω1]
  constructor
  · rw [div_eq_iff hdet]; ring
  · rw [div_eq_iff hdet]; ring

end Fig511

/-! ### Primer, Figure 3.13: total effect as a sum over directed paths -/

namespace PrimerFig313

/-- The graph with `X = 0`, `Z = 1`, `W = 2`, `Y = 3` and edges `X → Z`, `X → W`, `Z → W`,
`Z → Y`, `W → Y`. -/
def G : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨
    (i = 2 ∧ j = 3)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Figure 3.13 of the Primer: `Z = a X + U_Z`, `W = b X + c Z + U_W`, `Y = d Z + e W + U_Y`,
with an arbitrary symmetric error covariance `Ω`. -/
def model (a b c d e : ℝ) (Ω : Matrix (Fin 4) (Fin 4) ℝ) (hΩ : Ωᵀ = Ω) : LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; a, 0, 0, 0; b, c, 0, 0; 0, d, e, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := Ω
  Ω_symm := hΩ

/-- The total effect of `Z` on `Y` is `τ = d + e c`, the sum of the products of the coefficients
along the two directed paths `Z → Y` and `Z → W → Y`, whatever the error covariance (Primer,
Section 3.8.2); by `LinearSEM.intervene_value` it is the slope of `Y` under `do(Z = z)`. -/
theorem total_effect (a b c d e : ℝ) (Ω : Matrix (Fin 4) (Fin 4) ℝ) (hΩ : Ωᵀ = Ω) :
    (model a b c d e Ω hΩ).T 3 1 = d + e * c := by
  rw [T_eq_of_mul_eq_one (model a b c d e Ω hΩ) (A := !![1, 0, 0, 0; a, 1, 0, 0;
    b + c * a, c, 1, 0; d * a + e * (b + c * a), d + e * c, e, 1])]
  · rfl
  · ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]
    all_goals ring

end PrimerFig313

/-! ### Primer, Figure 3.14: total effect by back-door adjustment -/

namespace PrimerFig314

/-- The graph with `T = 0`, `X = 1`, `W = 2`, `Y = 3` and edges `T → X`, `T → Y`, `X → W`,
`W → Y`. -/
def G : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Figure 3.14 of the Primer: `X = α T + U_X`, `W = γ X + U_W`, `Y = β T + δ W + U_Y`, with
independent errors. -/
def model (α β γ δ ω0 ω1 ω2 ω3 : ℝ) : LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; α, 0, 0, 0; 0, γ, 0, 0; β, 0, δ, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := !![ω0, 0, 0, 0; 0, ω1, 0, 0; 0, 0, ω2, 0; 0, 0, 0, ω3]
  Ω_symm := by ext i j; fin_cases i <;> fin_cases j <;> rfl

variable (α β γ δ ω0 ω1 ω2 ω3 : ℝ)

theorem T_eq : (model α β γ δ ω0 ω1 ω2 ω3).T =
    !![1, 0, 0, 0; α, 1, 0, 0; γ * α, γ, 1, 0; β + δ * γ * α, δ * γ, δ, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]
    ring

theorem cov_eq (i j : Fin 4) : (model α β γ δ ω0 ω1 ω2 ω3).cov i j =
    ∑ k, ∑ l, (!![1, 0, 0, 0; α, 1, 0, 0; γ * α, γ, 1, 0; β + δ * γ * α, δ * γ, δ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) i k *
      (!![ω0, 0, 0, 0; 0, ω1, 0, 0; 0, 0, ω2, 0; 0, 0, 0, ω3] : Matrix (Fin 4) (Fin 4) ℝ) k l *
      (!![1, 0, 0, 0; α, 1, 0, 0; γ * α, γ, 1, 0; β + δ * γ * α, δ * γ, δ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) j l := by
  rw [cov_apply, T_eq]; rfl

theorem det_XT : (model α β γ δ ω0 ω1 ω2 ω3).cov 1 1 * (model α β γ δ ω0 ω1 ω2 ω3).cov 0 0 -
    (model α β γ δ ω0 ω1 ω2 ω3).cov 1 0 ^ 2 = ω1 * ω0 := by
  simp [cov_eq, Fin.sum_univ_four]; ring

/-- Primer, Figure 3.14: `X` has no direct effect on `Y`, its total effect is `γ δ`, and the
coefficient of `X` in the regression of `Y` on `X` and the back-door set `{T}` is `γ δ`, without
measuring `W`. -/
theorem regression_X_eq (hω0 : ω0 ≠ 0) (hω1 : ω1 ≠ 0) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α β γ δ ω0 ω1 ω2 ω3).cov {1, 0} 3 r) :
    r 1 = (model α β γ δ ω0 ω1 ω2 ω3).T 3 1 ∧ (model α β γ δ ω0 ω1 ω2 ω3).T 3 1 = γ * δ := by
  have hD := (det_XT α β γ δ ω0 ω1 ω2 ω3).symm ▸ mul_ne_zero hω1 hω0
  rw [((isRegCoeff_pair_iff (by decide) ((model α β γ δ ω0 ω1 ω2 ω3).cov_symm 0 1) hD).1 hr).2.1,
    det_XT, T_eq, div_eq_iff (mul_ne_zero hω1 hω0)]
  simp [cov_eq, Fin.sum_univ_four]
  constructor <;> ring

/-- Without adjustment for `T` the slope is biased by the back-door path `X ← T → Y`:
`r_YX = γ δ + α β ω_T / Var(X)`. -/
theorem slope_XY (hx : α ^ 2 * ω0 + ω1 ≠ 0) :
    regSlope (model α β γ δ ω0 ω1 ω2 ω3).cov 1 3 = γ * δ + α * β * ω0 / (α ^ 2 * ω0 + ω1) := by
  have h11 : (model α β γ δ ω0 ω1 ω2 ω3).cov 1 1 = α ^ 2 * ω0 + ω1 := by
    simp [cov_eq, Fin.sum_univ_four]; ring
  have h13 : (model α β γ δ ω0 ω1 ω2 ω3).cov 1 3 =
      γ * δ * (α ^ 2 * ω0 + ω1) + α * β * ω0 := by
    simp [cov_eq, Fin.sum_univ_four]; ring
  rw [regSlope, h11, h13]
  field_simp

/-- The failure case: when the back-door path is active (`α β ω_T ≠ 0`), the unadjusted slope is
not the total effect. -/
theorem slope_XY_ne (hx : α ^ 2 * ω0 + ω1 ≠ 0) (h : α * β * ω0 ≠ 0) :
    regSlope (model α β γ δ ω0 ω1 ω2 ω3).cov 1 3 ≠ γ * δ := by
  rw [slope_XY α β γ δ ω0 ω1 ω2 ω3 hx]
  intro h'
  exact h (by simpa [hx] using h')

end PrimerFig314

/-! ### Primer, Figure 3.15: direct effect by the regression rule -/

namespace PrimerFig315

/-- The graph with `Z = 0`, `X = 1`, `W = 2`, `Y = 3` and edges `Z → X`, `X → W`, `W → Y`,
`X → Y`. -/
def G : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨ (i = 1 ∧ j = 3)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Figure 3.15 of the Primer: `X = β Z + U_X`, `W = γ X + U_W`, `Y = α X + δ W + U_Y`, with
independent errors. -/
def model (α β γ δ ω0 ω1 ω2 ω3 : ℝ) : LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; β, 0, 0, 0; 0, γ, 0, 0; 0, α, δ, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := !![ω0, 0, 0, 0; 0, ω1, 0, 0; 0, 0, ω2, 0; 0, 0, 0, ω3]
  Ω_symm := by ext i j; fin_cases i <;> fin_cases j <;> rfl

variable (α β γ δ ω0 ω1 ω2 ω3 : ℝ)

theorem T_eq : (model α β γ δ ω0 ω1 ω2 ω3).T =
    !![1, 0, 0, 0; β, 1, 0, 0; γ * β, γ, 1, 0; (α + δ * γ) * β, α + δ * γ, δ, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]
    all_goals ring

theorem cov_eq (i j : Fin 4) : (model α β γ δ ω0 ω1 ω2 ω3).cov i j =
    ∑ k, ∑ l, (!![1, 0, 0, 0; β, 1, 0, 0; γ * β, γ, 1, 0; (α + δ * γ) * β, α + δ * γ, δ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) i k *
      (!![ω0, 0, 0, 0; 0, ω1, 0, 0; 0, 0, ω2, 0; 0, 0, 0, ω3] : Matrix (Fin 4) (Fin 4) ℝ) k l *
      (!![1, 0, 0, 0; β, 1, 0, 0; γ * β, γ, 1, 0; (α + δ * γ) * β, α + δ * γ, δ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) j l := by
  rw [cov_apply, T_eq]; rfl

theorem det_XW : (model α β γ δ ω0 ω1 ω2 ω3).cov 1 1 * (model α β γ δ ω0 ω1 ω2 ω3).cov 2 2 -
    (model α β γ δ ω0 ω1 ω2 ω3).cov 1 2 ^ 2 = (β ^ 2 * ω0 + ω1) * ω2 := by
  simp [cov_eq, Fin.sum_univ_four]; ring

/-- Primer, Figures 3.15 and 3.16: `W` d-separates `X` and `Y` once `X → Y` is deleted, and the
coefficient of `X` in the regression of `Y` on `X` and `W` is the direct effect `α`. -/
theorem regression_X_eq (hx : β ^ 2 * ω0 + ω1 ≠ 0) (hω2 : ω2 ≠ 0) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α β γ δ ω0 ω1 ω2 ω3).cov {1, 2} 3 r) : r 1 = α := by
  have hD := (det_XW α β γ δ ω0 ω1 ω2 ω3).symm ▸ mul_ne_zero hx hω2
  rw [((isRegCoeff_pair_iff (by decide) ((model α β γ δ ω0 ω1 ω2 ω3).cov_symm 2 1) hD).1 hr).2.1,
    det_XW, div_eq_iff (mul_ne_zero hx hω2)]
  simp [cov_eq, Fin.sum_univ_four]
  ring

end PrimerFig315

end LinearSEM

end CausalInference
