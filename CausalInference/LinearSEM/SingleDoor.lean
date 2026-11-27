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
`Y` and `Z` d-separates `X` from `Y` in the graph with `X → Y` deleted. For uncorrelated errors
the graphical theorem is `LinearSEM.single_door` in `CausalInference.LinearSEM.DSeparation`.
For correlated errors it needs a bridge from d-separation in a path diagram with bidirected arcs
to vanishing partial covariance; it is proved in `CausalInference.LinearSEM.CorrelatedErrors`
for correlated errors given by latent common causes, not for an arbitrary error covariance.
What is proved here, for any error covariance, is its algebraic core: Pearl's decomposition
`r_YX·S = α + I_YX·S` (`LinearSEM.isRegCoeff_decomposition`, `LinearSEM.regCoeff_eq_add`), where
`I_YX·S` is computed in the model with the coefficient `α` deleted (`LinearSEM.deleteCoeff`), and
its consequence `LinearSEM.single_door_of_partialCov`: if the partial covariance of `X` and `Y`
given `Z` vanishes in that model, then `α = r_YX·Z`. d-separation in the directed graph alone
yields that vanishing only for uncorrelated errors (or when correlated errors are drawn as
bidirected arcs); `DescendantExample.counterexample` shows that the condition that `Z` contains no
descendant of `Y` cannot be dropped. The precursors for uncorrelated errors are in
`CausalInference.LinearSEM.PathCoefficients`. This file also checks the books' worked examples,
with symbolic coefficients, by direct covariance algebra: each model is a `LinearSEM` on `Fin n`,
its total effect matrix is computed by `LinearSEM.T_eq_of_mul_eq_one`, and each claimed identity
between a structural coefficient and a regression coefficient is proved from the implied
covariance matrix.

Each graph of Pearl (2009) below, with its bidirected arcs and its coefficient labels, follows the
printed Figures 5.7 to 5.11 (where a model is more general than the printed figure, its docstring
says so and the printed case is stated separately); the Primer graphs follow the prose of the
Primer, Section 3.8. Each graph is stated in the docstring of its model.

## Examples

* `DescendantExample`: `X → Y → Z`; with `Z` a descendant of `Y` the single-door conclusion fails
  although the vanishing partial covariance holds.
* `Fig57`: `Z → X → Y` (`β`, `α`), `Z ↔ Y`: `α = r_YX·Z` and `β = r_XZ`.
* `Fig58`: `Z₂ → X`, `Z₂ → Y`, `X ↔ Z₂`, `X → Z₁ → Y` (`β`, `γ`), `Z₁ ↔ Y`, `X → Y` (`α`): the
  total effect `α + β γ = r_YX·Z₂`.
* `Fig59`: `Z → X → Y`, `X ↔ Y`: the instrumental variable formula `α = r_YZ / r_XZ`, while the
  plain slope `r_YX` differs from `α` when `Cov(ε_X, ε_Y) ≠ 0`.
* `Fig510`: `X → W → Y`, `X → Z → Y`, `X ↔ Z`, `W ↔ Y`: `α β = r_YX·Z`, `α = r_WX`,
  `β = r_YX·Z / r_WX`, `γ = r_YZ·X`; `Fig510.numeric_check`: with `W ↔ Y` active the regression
  of `Y` on `W` and `Z` does not return `β`.
* `Fig511`: two instruments `X`, `X'` for two treatments `Z`, `W` of `Y`, arcs `Z ↔ Y`, `W ↔ Y`:
  `β` and `δ` solve a 2 by 2 linear system of slopes, identified when its determinant is
  nonzero.
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
  Ω_posSemidef := M.Ω_posSemidef

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
of `x` and `y` given `Z` vanishes. Then `α` is the coefficient of `x` in the regression of `y` on
`x` and `Z`. Any error covariance is allowed.

The vanishing partial covariance is what d-separation of `x` and `y` by `Z` in `G_α` delivers,
but only when the errors are uncorrelated (diagonal `Ω`), or when every correlated pair of errors
is represented in the graph as a bidirected arc. For the directed graph `M.G` alone with
correlated errors the implication is false: in the bow (`Bow.model`, `x → y` with
`Cov(ε_x, ε_y) = ω ≠ 0`), deleting `x → y` leaves `x` and `y` d-separated by `∅`, yet the
covariance of `x` and `y` in the deleted model is `ω`. The hypothesis that no variable of
`insert x Z` is reachable from `y` cannot be dropped: see
`DescendantExample.counterexample`. The graphical form for uncorrelated errors is
`LinearSEM.single_door` in `CausalInference.LinearSEM.DSeparation`. -/
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

/-! ### Conditioning on a descendant of the outcome -/

namespace DescendantExample

/-- The chain `X → Y → Z` with `X = 0`, `Y = 1`, `Z = 2`. -/
def G : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- `X = ε_X`, `Y = X + ε_Y`, `Z = Y + ε_Z`, with uncorrelated unit errors. -/
def model : LinearSEM (Fin 3) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0; 1, 0, 0; 0, 1, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := 1
  Ω_posSemidef := Matrix.PosSemidef.one

theorem T_eq : model.T = !![1, 0, 0; 1, 1, 0; 1, 1, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_three]

theorem T_deleteCoeff_eq : (model.deleteCoeff 1 0).T = !![1, 0, 0; 0, 1, 0; 0, 1, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [model, deleteCoeff_B_apply, Matrix.mul_apply, Fin.sum_univ_three]

/-- The single-door conclusion fails when `Z` contains a descendant of the outcome. With
`Z = {Z}`: in the model with `X → Y` deleted, `X` is isolated, so it is d-separated from `Y` by
`Z` (proved as `DescendantExample.dSep_deleteEdgeGraph` in
`CausalInference.LinearSEM.DSeparation`, where `DescendantExample.counterexample_single_door`
checks every other hypothesis of `single_door`) and the partial covariance of `X` and `Y`
given `Z` vanishes; both covariance blocks are invertible; but `Z` is a descendant of `Y`, and
the coefficient of `X` in the regression of `Y` on `X` and `Z` is `1 / 2`,
while the path coefficient is `1`. -/
theorem counterexample :
    partialCov (model.deleteCoeff 1 0).cov {2} 0 1 = 0 ∧ IsUnit (subCov model.cov {2}) ∧
      IsUnit (subCov model.cov (insert 0 {2})) ∧ Relation.ReflTransGen model.G.Adj 1 2 ∧
      regCoeff model.cov (insert 0 {2}) 1 0 = 1 / 2 ∧ model.B 1 0 = 1 := by
  have hpd : model.cov.PosDef := model.cov_posDef Matrix.PosDef.one
  have hu := isUnit_submatrix_of_posDef hpd
  have hC : ∀ i j, model.cov i j = ∑ a, ∑ b, (!![1, 0, 0; 1, 1, 0; 1, 1, 1] :
      Matrix (Fin 3) (Fin 3) ℝ) i a * (1 : Matrix (Fin 3) (Fin 3) ℝ) a b *
      (!![1, 0, 0; 1, 1, 0; 1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ) j b := by
    intro i j; rw [cov_apply, T_eq]; rfl
  refine ⟨?_, hu _, hu _, Relation.ReflTransGen.single (Or.inr ⟨rfl, rfl⟩), ?_, rfl⟩
  · have hD : ∀ j, (model.deleteCoeff 1 0).cov 0 j = if j = 0 then 1 else 0 := by
      intro j
      rw [cov_apply, T_deleteCoeff_eq]
      fin_cases j <;> simp [deleteCoeff, model, Fin.sum_univ_three, Matrix.one_apply]
    rw [partialCov, Fin.sum_univ_three]
    simp [hD, regCoeff]
  · have hr := regCoeff_isRegCoeff 1 (hu (insert 0 {2}))
    have hD : model.cov 0 0 * model.cov 2 2 - model.cov 0 2 ^ 2 ≠ 0 := by
      simp [hC, Fin.sum_univ_three, Matrix.one_apply]
    rw [((isRegCoeff_pair_iff (by decide) (model.cov_symm 2 0) hD).1 hr).2.1]
    simp [hC, Fin.sum_univ_three, Matrix.one_apply]; norm_num

end DescendantExample

/-! ### Figure 5.7 -/

namespace Fig57

/-- The graph `Z → X → Y` with `Z = 0`, `X = 1`, `Y = 2`. -/
def G : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The error covariance of Figure 5.7, with the bidirected arc `Z ↔ Y`. -/
abbrev errCov (ωz ωx ωy ωzy : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ωz, 0, ωzy; 0, ωx, 0; ωzy, 0, ωy]

/-- Figure 5.7 of Pearl (2009), with the printed labels: `X = β Z + ε_X`, `Y = α X + ε_Y`, with
`Cov(ε_Z, ε_Y) = ω_ZY` (the bidirected arc `Z ↔ Y`). -/
def model (α β ωz ωx ωy ωzy : ℝ) (hΩ : (errCov ωz ωx ωy ωzy).PosSemidef) :
    LinearSEM (Fin 3) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0; β, 0, 0; 0, α, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := errCov ωz ωx ωy ωzy
  Ω_posSemidef := hΩ

variable (α β ωz ωx ωy ωzy : ℝ) (hΩ : (errCov ωz ωx ωy ωzy).PosSemidef)

theorem T_eq : (model α β ωz ωx ωy ωzy hΩ).T = !![1, 0, 0; β, 1, 0; β * α, α, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_three]
    ring

theorem cov_eq (i j : Fin 3) : (model α β ωz ωx ωy ωzy hΩ).cov i j =
    ∑ a, ∑ b, (!![1, 0, 0; β, 1, 0; β * α, α, 1] : Matrix (Fin 3) (Fin 3) ℝ) i a *
      (!![ωz, 0, ωzy; 0, ωx, 0; ωzy, 0, ωy] : Matrix (Fin 3) (Fin 3) ℝ) a b *
      (!![1, 0, 0; β, 1, 0; β * α, α, 1] : Matrix (Fin 3) (Fin 3) ℝ) j b := by
  rw [cov_apply, T_eq]; rfl

theorem det_XZ : (model α β ωz ωx ωy ωzy hΩ).cov 1 1 * (model α β ωz ωx ωy ωzy hΩ).cov 0 0 -
    (model α β ωz ωx ωy ωzy hΩ).cov 1 0 ^ 2 = ωx * ωz := by
  simp [cov_eq, Fin.sum_univ_three]; ring

/-- Figure 5.7, single door for `α`: `Z` d-separates `X` and `Y` once `X → Y` is deleted, and the
coefficient of `X` in the regression of `Y` on `X` and `Z` is `α = r_YX·Z`. -/
theorem regression_X_eq (hωx : ωx ≠ 0) (hωz : ωz ≠ 0) {r : Fin 3 → ℝ}
    (hr : IsRegCoeff (model α β ωz ωx ωy ωzy hΩ).cov {1, 0} 2 r) : r 1 = α := by
  have hD := (det_XZ α β ωz ωx ωy ωzy hΩ).symm ▸ mul_ne_zero hωx hωz
  rw [((isRegCoeff_pair_iff (by decide) ((model α β ωz ωx ωy ωzy hΩ).cov_symm 0 1) hD).1
    hr).2.1, det_XZ, div_eq_iff (mul_ne_zero hωx hωz)]
  simp [cov_eq, Fin.sum_univ_three]
  ring

/-- Figure 5.7, single door for `β`: `Z` and `X` are d-separated by the empty set once `Z → X` is
deleted, and `β = r_XZ`. -/
theorem slope_ZX (hωz : ωz ≠ 0) : regSlope (model α β ωz ωx ωy ωzy hΩ).cov 0 1 = β := by
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

/-- The error covariance of Figure 5.8, with the bidirected arcs `X ↔ Z₂` and `Z₁ ↔ Y`. -/
abbrev errCov (ω0 ω1 ω2 ω3 ωxz ωzy : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ω0, ωxz, 0, 0; ωxz, ω1, 0, 0; 0, 0, ω2, ωzy; 0, 0, ωzy, ω3]

/-- Figure 5.8 of Pearl (2009), with the printed labels `α` (`X → Y`), `β` (`X → Z₁`) and `γ`
(`Z₁ → Y`); the coefficients `a` (`Z₂ → X`) and `b` (`Z₂ → Y`) are unlabeled in the figure:
`X = a Z₂ + ε_X`, `Z₁ = β X + ε_Z₁`, `Y = b Z₂ + α X + γ Z₁ + ε_Y`, with bidirected arcs
`X ↔ Z₂` (`ω_XZ`) and `Z₁ ↔ Y` (`ω_ZY`). -/
def model (a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy : ℝ)
    (hΩ : (errCov ω0 ω1 ω2 ω3 ωxz ωzy).PosSemidef) : LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; a, 0, 0, 0; 0, β, 0, 0; b, α, γ, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := errCov ω0 ω1 ω2 ω3 ωxz ωzy
  Ω_posSemidef := hΩ

variable (a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy : ℝ) (hΩ : (errCov ω0 ω1 ω2 ω3 ωxz ωzy).PosSemidef)

/-- The total effect matrix; entry `(Y, X)` is `α + β γ`. -/
theorem T_eq : (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy hΩ).T =
    !![1, 0, 0, 0; a, 1, 0, 0; β * a, β, 1, 0; b + a * (α + β * γ), α + β * γ, γ, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]
    all_goals ring

theorem cov_eq (i j : Fin 4) : (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy hΩ).cov i j =
    ∑ k, ∑ l, (!![1, 0, 0, 0; a, 1, 0, 0; β * a, β, 1, 0; b + a * (α + β * γ), α + β * γ, γ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) i k *
      (!![ω0, ωxz, 0, 0; ωxz, ω1, 0, 0; 0, 0, ω2, ωzy; 0, 0, ωzy, ω3] :
        Matrix (Fin 4) (Fin 4) ℝ) k l *
      (!![1, 0, 0, 0; a, 1, 0, 0; β * a, β, 1, 0; b + a * (α + β * γ), α + β * γ, γ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) j l := by
  rw [cov_apply, T_eq]; rfl

theorem det_XZ2 : (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy hΩ).cov 1 1 *
    (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy hΩ).cov 0 0 -
    (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy hΩ).cov 1 0 ^ 2 = ω0 * ω1 - ωxz ^ 2 := by
  simp [cov_eq, Fin.sum_univ_four]; ring

/-- Figure 5.8, back door for the total effect: `Z₂` blocks the back-door paths `X ← Z₂ → Y`
and `X ↔ Z₂ → Y`, and the coefficient of `X` in the regression of `Y` on `X` and `Z₂` is the
total effect `α + β γ = r_YX·Z₂`, although `α` itself is not identified by single door. The
hypothesis `ω0 ω1 ≠ ω_XZ ²` says the errors of `Z₂` and `X` are not perfectly correlated. -/
theorem regression_X_eq (hD : ω0 * ω1 - ωxz ^ 2 ≠ 0) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy hΩ).cov {1, 0} 3 r) :
    r 1 = α + β * γ := by
  have hD' := (det_XZ2 a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy hΩ).symm ▸ hD
  rw [((isRegCoeff_pair_iff (by decide)
    ((model a b α β γ ω0 ω1 ω2 ω3 ωxz ωzy hΩ).cov_symm 0 1) hD').1 hr).2.1, det_XZ2,
    div_eq_iff hD]
  simp [cov_eq, Fin.sum_univ_four]
  ring

end Fig58

/-! ### Figure 5.9 -/

namespace Fig59

/-- The graph `Z → X → Y` with `Z = 0`, `X = 1`, `Y = 2`. -/
def G : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The error covariance of Figure 5.9, with the bidirected arc `X ↔ Y`. -/
abbrev errCov (ωz ωx ωy ωxy : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ωz, 0, 0; 0, ωx, ωxy; 0, ωxy, ωy]

/-- Figure 5.9 of Pearl (2009) (and Figure 3.17 of the Primer): `X = β Z + ε_X`,
`Y = α X + ε_Y`, with `Cov(ε_X, ε_Y) = ω_XY` (the bidirected arc `X ↔ Y`); `Z` is an
instrument. -/
def model (α β ωz ωx ωy ωxy : ℝ) (hΩ : (errCov ωz ωx ωy ωxy).PosSemidef) :
    LinearSEM (Fin 3) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0; β, 0, 0; 0, α, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := errCov ωz ωx ωy ωxy
  Ω_posSemidef := hΩ

variable (α β ωz ωx ωy ωxy : ℝ) (hΩ : (errCov ωz ωx ωy ωxy).PosSemidef)

theorem T_eq : (model α β ωz ωx ωy ωxy hΩ).T = !![1, 0, 0; β, 1, 0; α * β, α, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_three]

theorem cov_eq (i j : Fin 3) : (model α β ωz ωx ωy ωxy hΩ).cov i j =
    ∑ a, ∑ b, (!![1, 0, 0; β, 1, 0; α * β, α, 1] : Matrix (Fin 3) (Fin 3) ℝ) i a *
      (!![ωz, 0, 0; 0, ωx, ωxy; 0, ωxy, ωy] : Matrix (Fin 3) (Fin 3) ℝ) a b *
      (!![1, 0, 0; β, 1, 0; α * β, α, 1] : Matrix (Fin 3) (Fin 3) ℝ) j b := by
  rw [cov_apply, T_eq]; rfl

/-- The instrumental variable formula (Pearl 2009, Figure 5.9 and equation (3.46)): the ratio of
the slopes of `Y` and of `X` on the instrument `Z` is the path coefficient,
`α = r_YZ / r_XZ`. -/
theorem iv_formula (hβ : β ≠ 0) (hωz : ωz ≠ 0) :
    regSlope (model α β ωz ωx ωy ωxy hΩ).cov 0 2 /
      regSlope (model α β ωz ωx ωy ωxy hΩ).cov 0 1 = α := by
  simp [regSlope, cov_eq, Fin.sum_univ_three]
  field_simp

/-- The same identity through the general theorem `LinearSEM.iv_ratio`. -/
theorem iv_formula' (hβ : β ≠ 0) (hωz : ωz ≠ 0) :
    (model α β ωz ωx ωy ωxy hΩ).cov 0 2 / (model α β ωz ωx ωy ωxy hΩ).cov 0 1 = α := by
  refine (model α β ωz ωx ωy ωxy hΩ).iv_ratio (x := 1) (fun p => ?_) ?_ ?_
  · fin_cases p <;> simp [model]
  · rw [Matrix.mul_apply, T_eq]; simp [model, Fin.sum_univ_three]
  · simp [cov_eq, Fin.sum_univ_three, hβ, hωz]

/-- Without the instrument, the slope `r_YX` is biased by the confounding arc:
`r_YX = α + ω_XY / Var(X)` with `Var(X) = β ² ω_Z + ω_X`. -/
theorem slope_XY (hx : β ^ 2 * ωz + ωx ≠ 0) :
    regSlope (model α β ωz ωx ωy ωxy hΩ).cov 1 2 = α + ωxy / (β ^ 2 * ωz + ωx) := by
  have h11 : (model α β ωz ωx ωy ωxy hΩ).cov 1 1 = β ^ 2 * ωz + ωx := by
    simp [cov_eq, Fin.sum_univ_three]; ring
  have h12 : (model α β ωz ωx ωy ωxy hΩ).cov 1 2 = α * (β ^ 2 * ωz + ωx) + ωxy := by
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

/-- The error covariance of Figure 5.10, with the two bidirected arcs `X ↔ Z` and `W ↔ Y`. -/
abbrev errCov (ω0 ω1 ω2 ω3 ωxz ωwy : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ω0, 0, ωxz, 0; 0, ω1, 0, ωwy; ωxz, 0, ω2, 0; 0, ωwy, 0, ω3]

/-- Figure 5.10 of Pearl (2009): `W = α X + ε_W`, `Z = δ X + ε_Z`, `Y = β W + γ Z + ε_Y`, with the
two printed bidirected arcs `X ↔ Z` (`ω_XZ`) and `W ↔ Y` (`ω_WY`). The total effect `α β + γ δ`
of `X` on `Y` is not identified by the back-door criterion, and the arc `W ↔ Y` prevents the
identification of `β` by regressing `Y` on `W` (`numeric_check`). -/
def model (α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy : ℝ) (hΩ : (errCov ω0 ω1 ω2 ω3 ωxz ωwy).PosSemidef) :
    LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; α, 0, 0, 0; δ, 0, 0, 0; 0, β, γ, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := errCov ω0 ω1 ω2 ω3 ωxz ωwy
  Ω_posSemidef := hΩ

variable (α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy : ℝ) (hΩ : (errCov ω0 ω1 ω2 ω3 ωxz ωwy).PosSemidef)

/-- The total effect matrix; entry `(Y, X)` is `α β + γ δ`. -/
theorem T_eq : (model α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).T =
    !![1, 0, 0, 0; α, 1, 0, 0; δ, 0, 1, 0; α * β + γ * δ, β, γ, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]
    ring

theorem cov_eq (i j : Fin 4) : (model α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).cov i j =
    ∑ k, ∑ l, (!![1, 0, 0, 0; α, 1, 0, 0; δ, 0, 1, 0; α * β + γ * δ, β, γ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) i k *
      (!![ω0, 0, ωxz, 0; 0, ω1, 0, ωwy; ωxz, 0, ω2, 0; 0, ωwy, 0, ω3] :
        Matrix (Fin 4) (Fin 4) ℝ) k l *
      (!![1, 0, 0, 0; α, 1, 0, 0; δ, 0, 1, 0; α * β + γ * δ, β, γ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) j l := by
  rw [cov_apply, T_eq]; rfl

theorem det_XZ : (model α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).cov 0 0 *
    (model α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).cov 2 2 -
    (model α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).cov 0 2 ^ 2 = ω0 * ω2 - ωxz ^ 2 := by
  simp [cov_eq, Fin.sum_univ_four]; ring

/-- Figure 5.10: conditioning on `Z` blocks every path through `Z`, so the coefficient of `X` in
the regression of `Y` on `X` and `Z` is the effect `α β` mediated by `W`, and conditioning on `X`
blocks the back-door paths from `Z`, so the coefficient of `Z` is `γ = r_YZ·X`. Both hold with
the arc `W ↔ Y` present. -/
theorem regression_eq (hD : ω0 * ω2 - ωxz ^ 2 ≠ 0) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).cov {0, 2} 3 r) :
    r 0 = α * β ∧ r 2 = γ := by
  have hD' := (det_XZ α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).symm ▸ hD
  obtain ⟨-, h0, h2⟩ := (isRegCoeff_pair_iff (by decide)
    ((model α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).cov_symm 2 0) hD').1 hr
  rw [det_XZ] at h0 h2
  rw [h0, h2, div_eq_iff hD, div_eq_iff hD]
  constructor
  · simp [cov_eq, Fin.sum_univ_four]; ring
  · simp [cov_eq, Fin.sum_univ_four]; ring

/-- Figure 5.10: there is no back-door path from `X` to `W`, so `α = r_WX`. -/
theorem slope_XW (hω0 : ω0 ≠ 0) :
    regSlope (model α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).cov 0 1 = α := by
  rw [regSlope, div_eq_iff (by simpa [cov_eq, Fin.sum_univ_four] using hω0)]
  simp [cov_eq, Fin.sum_univ_four]
  ring

/-- Figure 5.10: `β = r_YX·Z / r_WX`. -/
theorem beta_eq (hD : ω0 * ω2 - ωxz ^ 2 ≠ 0) (hω0 : ω0 ≠ 0) (hα : α ≠ 0) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).cov {0, 2} 3 r) :
    r 0 / regSlope (model α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ).cov 0 1 = β := by
  rw [(regression_eq α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ hD hr).1,
    slope_XW α β γ δ ω0 ω1 ω2 ω3 ωxz ωwy hΩ hω0]
  field_simp

/-- The error covariance with unit variances, `ω_XZ = 1 / 3` and `ω_WY = 1 / 2` is positive
semidefinite: it is `L D Lᵀ` with `D` diagonal and nonnegative. -/
theorem numeric_posSemidef : (errCov 1 1 1 1 (1 / 3) (1 / 2)).PosSemidef := by
  have h := (Matrix.PosSemidef.diagonal (d := ![1 / 3, 1 / 2, 2 / 3, 1 / 2, 2 / 3, 1 / 2])
    (fun i => by fin_cases i <;> norm_num)).mul_mul_conjTranspose_same
    (!![1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0; 1, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 6) ℝ)
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul_diagonal, Fin.sum_univ_succ] <;> norm_num

/-- A numeric check of Figure 5.10 with the arc `W ↔ Y` active: all four path coefficients and
all error variances equal to one, `ω_XZ = 1 / 3`, `ω_WY = 1 / 2`. Regressing `Y` on `W` and `Z`
gives the coefficient `11 / 8` on `W`, not `β = 1`, while Pearl's ratio `r_YX·Z / r_WX` returns
`β = 1`. -/
theorem numeric_check :
    (∀ r : Fin 4 → ℝ,
      IsRegCoeff (model 1 1 1 1 1 1 1 1 (1 / 3) (1 / 2) numeric_posSemidef).cov {1, 2} 3 r →
        r 1 = 11 / 8) ∧
    (∀ r : Fin 4 → ℝ,
      IsRegCoeff (model 1 1 1 1 1 1 1 1 (1 / 3) (1 / 2) numeric_posSemidef).cov {0, 2} 3 r →
        r 0 / regSlope (model 1 1 1 1 1 1 1 1 (1 / 3) (1 / 2) numeric_posSemidef).cov 0 1 =
          1) := by
  refine ⟨fun r hr => ?_, fun r hr => beta_eq _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num) hr⟩
  have hD : (model 1 1 1 1 1 1 1 1 (1 / 3) (1 / 2) numeric_posSemidef).cov 1 1 *
      (model 1 1 1 1 1 1 1 1 (1 / 3) (1 / 2) numeric_posSemidef).cov 2 2 -
      (model 1 1 1 1 1 1 1 1 (1 / 3) (1 / 2) numeric_posSemidef).cov 1 2 ^ 2 ≠ 0 := by
    simp [cov_eq, Fin.sum_univ_four]; norm_num
  rw [((isRegCoeff_pair_iff (by decide)
    ((model 1 1 1 1 1 1 1 1 (1 / 3) (1 / 2) numeric_posSemidef).cov_symm 2 1) hD).1 hr).2.1]
  simp [cov_eq, Fin.sum_univ_four]; norm_num

end Fig510

/-! ### Figure 5.11 -/

namespace Fig511

/-- The graph with instruments `X = 0`, `X' = 1`, treatments `Z = 2`, `W = 3`, outcome `Y = 4`,
and edges from each instrument to each treatment and from each treatment to `Y`. -/
def G : Digraph (Fin 5) where
  Adj i j := (i.val < 2 ∧ (j = 2 ∨ j = 3)) ∨ ((i = 2 ∨ i = 3) ∧ j = 4)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The error covariance of Figure 5.11, with the printed arcs `Z ↔ Y` (`ω24`) and `W ↔ Y`
(`ω34`), and in addition an arc `Z ↔ W` (`ω23`) that the figure does not have. -/
abbrev errCov (ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ω0, 0, 0, 0, 0; 0, ω1, 0, 0, 0; 0, 0, ω2, ω23, ω24; 0, 0, ω23, ω3, ω34; 0, 0, ω24, ω34, ω4]

/-- Figure 5.11 of Pearl (2009), with the printed labels: `Z = α X + α' X' + ε_Z`,
`W = γ X + γ' X' + ε_W`, `Y = β Z + δ W + ε_Y`. The errors of `Z`, `W`, `Y` may be correlated
(the printed arcs `Z ↔ Y` and `W ↔ Y`, and, more generally than the figure, `Z ↔ W`; the printed
figure is `printed`, the case `ω23 = 0`); the errors of the instruments `X`, `X'` are
uncorrelated with the structural disturbances and with each other. -/
def model (α α' γ γ' β δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34 : ℝ)
    (hΩ : (errCov ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34).PosSemidef) : LinearSEM (Fin 5) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; α, α', 0, 0, 0; γ, γ', 0, 0, 0; 0, 0, β, δ, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := errCov ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34
  Ω_posSemidef := hΩ

/-- The model of the printed Figure 5.11: the only bidirected arcs are `Z ↔ Y` and `W ↔ Y`. -/
abbrev printed (α α' γ γ' β δ ω0 ω1 ω2 ω3 ω4 ω24 ω34 : ℝ)
    (hΩ : (errCov ω0 ω1 ω2 ω3 ω4 0 ω24 ω34).PosSemidef) : LinearSEM (Fin 5) :=
  model α α' γ γ' β δ ω0 ω1 ω2 ω3 ω4 0 ω24 ω34 hΩ

variable (α α' γ γ' β δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34 : ℝ)
  (hΩ : (errCov ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34).PosSemidef)

theorem T_eq : (model α α' γ γ' β δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34 hΩ).T =
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; α, α', 1, 0, 0; γ, γ', 0, 1, 0;
      β * α + δ * γ, β * α' + δ * γ', β, δ, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_five]
    all_goals ring

/-- The covariances of the instruments with the other variables. -/
theorem cov_instruments :
    let C := (model α α' γ γ' β δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34 hΩ).cov
    C 0 0 = ω0 ∧ C 1 1 = ω1 ∧ C 0 2 = α * ω0 ∧ C 1 2 = α' * ω1 ∧ C 0 3 = γ * ω0 ∧
      C 1 3 = γ' * ω1 ∧ C 0 4 = (β * α + δ * γ) * ω0 ∧ C 1 4 = (β * α' + δ * γ') * ω1 := by
  simp only [cov_apply, T_eq, Fin.sum_univ_five]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [model] <;> ring

/-- Figure 5.11: no single pair identifies `β` or `δ`, but the four instrument slopes
`r_ZX = α`, `r_ZX' = α'`, `r_WX = γ`, `r_WX' = γ'` and the two slopes `r_YX = α β + γ δ`,
`r_YX' = α' β + γ' δ` give two linear equations in `β` and `δ`, solvable when the determinant
`α γ' - γ α'` is nonzero: `β = (r_WX' r_YX - r_WX r_YX') / (r_ZX r_WX' - r_WX r_ZX')` and
`δ = (r_ZX r_YX' - r_ZX' r_YX) / (r_ZX r_WX' - r_WX r_ZX')`. -/
theorem identify (hω0 : ω0 ≠ 0) (hω1 : ω1 ≠ 0) (hdet : α * γ' - γ * α' ≠ 0) :
    let C := (model α α' γ γ' β δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34 hΩ).cov
    (regSlope C 1 3 * regSlope C 0 4 - regSlope C 0 3 * regSlope C 1 4) /
        (regSlope C 0 2 * regSlope C 1 3 - regSlope C 0 3 * regSlope C 1 2) = β ∧
      (regSlope C 0 2 * regSlope C 1 4 - regSlope C 1 2 * regSlope C 0 4) /
        (regSlope C 0 2 * regSlope C 1 3 - regSlope C 0 3 * regSlope C 1 2) = δ := by
  obtain ⟨h00, h11, h02, h12, h03, h13, h04, h14⟩ :=
    cov_instruments α α' γ γ' β δ ω0 ω1 ω2 ω3 ω4 ω23 ω24 ω34 hΩ
  simp only [regSlope, h00, h11, h02, h12, h03, h13, h04, h14, mul_div_cancel_right₀ _ hω0,
    mul_div_cancel_right₀ _ hω1]
  constructor
  · rw [div_eq_iff hdet]; ring
  · rw [div_eq_iff hdet]; ring

/-- Figure 5.11 as printed (arcs `Z ↔ Y` and `W ↔ Y` only): `β` and `δ` are identified by the
formulas of `identify`. -/
theorem identify_printed (hΩ : (errCov ω0 ω1 ω2 ω3 ω4 0 ω24 ω34).PosSemidef) (hω0 : ω0 ≠ 0)
    (hω1 : ω1 ≠ 0) (hdet : α * γ' - γ * α' ≠ 0) :
    let C := (printed α α' γ γ' β δ ω0 ω1 ω2 ω3 ω4 ω24 ω34 hΩ).cov
    (regSlope C 1 3 * regSlope C 0 4 - regSlope C 0 3 * regSlope C 1 4) /
        (regSlope C 0 2 * regSlope C 1 3 - regSlope C 0 3 * regSlope C 1 2) = β ∧
      (regSlope C 0 2 * regSlope C 1 4 - regSlope C 1 2 * regSlope C 0 4) /
        (regSlope C 0 2 * regSlope C 1 3 - regSlope C 0 3 * regSlope C 1 2) = δ :=
  identify α α' γ γ' β δ ω0 ω1 ω2 ω3 ω4 0 ω24 ω34 hΩ hω0 hω1 hdet

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
with an arbitrary (positive semidefinite) error covariance `Ω`. -/
def model (a b c d e : ℝ) (Ω : Matrix (Fin 4) (Fin 4) ℝ) (hΩ : Ω.PosSemidef) :
    LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; a, 0, 0, 0; b, c, 0, 0; 0, d, e, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := Ω
  Ω_posSemidef := hΩ

/-- The total effect of `Z` on `Y` is `τ = d + e c`, the sum of the products of the coefficients
along the two directed paths `Z → Y` and `Z → W → Y`, whatever the error covariance (Primer,
Section 3.8.2); by `LinearSEM.intervene_value` it is the slope of `Y` under `do(Z = z)`. -/
theorem total_effect (a b c d e : ℝ) (Ω : Matrix (Fin 4) (Fin 4) ℝ) (hΩ : Ω.PosSemidef) :
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

/-- The diagonal error covariance (uncorrelated errors). -/
abbrev errCov (ω0 ω1 ω2 ω3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ω0, 0, 0, 0; 0, ω1, 0, 0; 0, 0, ω2, 0; 0, 0, 0, ω3]

/-- Figure 3.14 of the Primer: `X = α T + U_X`, `W = γ X + U_W`, `Y = β T + δ W + U_Y`, with
uncorrelated errors. -/
def model (α β γ δ ω0 ω1 ω2 ω3 : ℝ) (hΩ : (errCov ω0 ω1 ω2 ω3).PosSemidef) :
    LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; α, 0, 0, 0; 0, γ, 0, 0; β, 0, δ, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := errCov ω0 ω1 ω2 ω3
  Ω_posSemidef := hΩ

variable (α β γ δ ω0 ω1 ω2 ω3 : ℝ) (hΩ : (errCov ω0 ω1 ω2 ω3).PosSemidef)

theorem T_eq : (model α β γ δ ω0 ω1 ω2 ω3 hΩ).T =
    !![1, 0, 0, 0; α, 1, 0, 0; γ * α, γ, 1, 0; β + δ * γ * α, δ * γ, δ, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]
    ring

theorem cov_eq (i j : Fin 4) : (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov i j =
    ∑ k, ∑ l, (!![1, 0, 0, 0; α, 1, 0, 0; γ * α, γ, 1, 0; β + δ * γ * α, δ * γ, δ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) i k *
      (!![ω0, 0, 0, 0; 0, ω1, 0, 0; 0, 0, ω2, 0; 0, 0, 0, ω3] : Matrix (Fin 4) (Fin 4) ℝ) k l *
      (!![1, 0, 0, 0; α, 1, 0, 0; γ * α, γ, 1, 0; β + δ * γ * α, δ * γ, δ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) j l := by
  rw [cov_apply, T_eq]; rfl

theorem det_XT : (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov 1 1 * (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov 0 0 -
    (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov 1 0 ^ 2 = ω1 * ω0 := by
  simp [cov_eq, Fin.sum_univ_four]; ring

/-- Primer, Figure 3.14: `X` has no direct effect on `Y`, its total effect is `γ δ`, and the
coefficient of `X` in the regression of `Y` on `X` and the back-door set `{T}` is `γ δ`, without
measuring `W`. -/
theorem regression_X_eq (hω0 : ω0 ≠ 0) (hω1 : ω1 ≠ 0) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov {1, 0} 3 r) :
    r 1 = (model α β γ δ ω0 ω1 ω2 ω3 hΩ).T 3 1 ∧ (model α β γ δ ω0 ω1 ω2 ω3 hΩ).T 3 1 = γ * δ := by
  have hD := (det_XT α β γ δ ω0 ω1 ω2 ω3 hΩ).symm ▸ mul_ne_zero hω1 hω0
  rw [((isRegCoeff_pair_iff (by decide) ((model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov_symm 0 1) hD).1 hr).2.1,
    det_XT, T_eq, div_eq_iff (mul_ne_zero hω1 hω0)]
  simp [cov_eq, Fin.sum_univ_four]
  constructor <;> ring

/-- Without adjustment for `T` the slope is biased by the back-door path `X ← T → Y`:
`r_YX = γ δ + α β ω_T / Var(X)`. -/
theorem slope_XY (hx : α ^ 2 * ω0 + ω1 ≠ 0) :
    regSlope (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov 1 3 = γ * δ + α * β * ω0 / (α ^ 2 * ω0 + ω1) := by
  have h11 : (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov 1 1 = α ^ 2 * ω0 + ω1 := by
    simp [cov_eq, Fin.sum_univ_four]; ring
  have h13 : (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov 1 3 =
      γ * δ * (α ^ 2 * ω0 + ω1) + α * β * ω0 := by
    simp [cov_eq, Fin.sum_univ_four]; ring
  rw [regSlope, h11, h13]
  field_simp

/-- The failure case: when the back-door path is active (`α β ω_T ≠ 0`), the unadjusted slope is
not the total effect. -/
theorem slope_XY_ne (hx : α ^ 2 * ω0 + ω1 ≠ 0) (h : α * β * ω0 ≠ 0) :
    regSlope (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov 1 3 ≠ γ * δ := by
  rw [slope_XY α β γ δ ω0 ω1 ω2 ω3 hΩ hx]
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

/-- The diagonal error covariance (uncorrelated errors). -/
abbrev errCov (ω0 ω1 ω2 ω3 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ω0, 0, 0, 0; 0, ω1, 0, 0; 0, 0, ω2, 0; 0, 0, 0, ω3]

/-- Figure 3.15 of the Primer: `X = β Z + U_X`, `W = γ X + U_W`, `Y = α X + δ W + U_Y`, with
uncorrelated errors. -/
def model (α β γ δ ω0 ω1 ω2 ω3 : ℝ) (hΩ : (errCov ω0 ω1 ω2 ω3).PosSemidef) :
    LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; β, 0, 0, 0; 0, γ, 0, 0; 0, α, δ, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := errCov ω0 ω1 ω2 ω3
  Ω_posSemidef := hΩ

variable (α β γ δ ω0 ω1 ω2 ω3 : ℝ) (hΩ : (errCov ω0 ω1 ω2 ω3).PosSemidef)

theorem T_eq : (model α β γ δ ω0 ω1 ω2 ω3 hΩ).T =
    !![1, 0, 0, 0; β, 1, 0, 0; γ * β, γ, 1, 0; (α + δ * γ) * β, α + δ * γ, δ, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]
    all_goals ring

theorem cov_eq (i j : Fin 4) : (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov i j =
    ∑ k, ∑ l, (!![1, 0, 0, 0; β, 1, 0, 0; γ * β, γ, 1, 0; (α + δ * γ) * β, α + δ * γ, δ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) i k *
      (!![ω0, 0, 0, 0; 0, ω1, 0, 0; 0, 0, ω2, 0; 0, 0, 0, ω3] : Matrix (Fin 4) (Fin 4) ℝ) k l *
      (!![1, 0, 0, 0; β, 1, 0, 0; γ * β, γ, 1, 0; (α + δ * γ) * β, α + δ * γ, δ, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) j l := by
  rw [cov_apply, T_eq]; rfl

theorem det_XW : (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov 1 1 * (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov 2 2 -
    (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov 1 2 ^ 2 = (β ^ 2 * ω0 + ω1) * ω2 := by
  simp [cov_eq, Fin.sum_univ_four]; ring

/-- Primer, Figures 3.15 and 3.16: `W` d-separates `X` and `Y` once `X → Y` is deleted, and the
coefficient of `X` in the regression of `Y` on `X` and `W` is the direct effect `α`. -/
theorem regression_X_eq (hx : β ^ 2 * ω0 + ω1 ≠ 0) (hω2 : ω2 ≠ 0) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov {1, 2} 3 r) : r 1 = α := by
  have hD := (det_XW α β γ δ ω0 ω1 ω2 ω3 hΩ).symm ▸ mul_ne_zero hx hω2
  rw [((isRegCoeff_pair_iff (by decide) ((model α β γ δ ω0 ω1 ω2 ω3 hΩ).cov_symm 2 1) hD).1 hr).2.1,
    det_XW, div_eq_iff (mul_ne_zero hx hω2)]
  simp [cov_eq, Fin.sum_univ_four]
  ring

end PrimerFig315

end LinearSEM

end CausalInference
