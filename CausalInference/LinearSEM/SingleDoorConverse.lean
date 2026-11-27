/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.DSeparation
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The converse of the single-door criterion: three failure patterns

Pearl's single-door criterion (Pearl 2009, Theorem 5.3.1) states that the path coefficient `α`
of `X → Y` equals the partial regression coefficient `r_YX·Z` when `Z` contains no descendant of
`Y` and d-separates `X` from `Y` in the graph with `X → Y` deleted; conversely, when these
conditions fail, the equality holds only on a set of parameters of measure zero. The sufficient
direction is `LinearSEM.single_door`. This file proves the converse, in its measure-zero form,
for the three minimal ways the conditions can fail, each as an explicit family of models with
uncorrelated errors and with all edge coefficients and positive error variances free:

* `Descendant`: `X → Y → W` with `Z = {W}` (a descendant of `Y` in `Z`; d-separation holds).
  The coefficient is `α σw / (β ^ 2 σy + σw)`, equal to `α` only when `α = 0` or `β = 0`.
* `BackDoorPath`: `C → X`, `C → Y`, `X → Y` with `Z = ∅` (an open back-door path). The slope is
  `α + γ δ σc / (γ ^ 2 σc + σx)`, equal to `α` only when `γ = 0` or `δ = 0`.
* `Collider`: `X → C ← U → Y`, `X → Y` with `Z = {C}` (a collider opened by `Z`). The
  coefficient is `α - a b d σu / (b ^ 2 σu + σc)`, equal to `α` only when `a`, `b` or `d` is zero.

In each family `isUnit_subCov` gives invertible covariance blocks for positive variances,
`witness` a parameter point where the regression coefficient and the path coefficient differ,
and `exceptional_null` shows that the set of parameter vectors with positive variances
at which the regression coefficient equals the path coefficient is Lebesgue null (it lies in a
finite union of coordinate hyperplanes), and `graph_facts` records which graphical condition
fails and which hold.

Not proved: the converse for an arbitrary DAG, edge `x → y` and set `Z`. The usual argument
would set unit coefficients along a d-connecting path and zero elsewhere to obtain one parameter
point with a nonzero bias, and then use that the bias times the regression determinant is a
polynomial in the parameters, whose zero set is null because the polynomial is nonzero. Neither
the general nonzero-bias construction nor a null-set theorem for zero sets of nonzero
multivariate polynomials is available here.

Source: J. Pearl (2009), *Causality*, 2nd edition, Section 5.3.1, Theorem 5.3.1.
-/

@[expose] public section

namespace CausalInference

namespace LinearSEM

open Matrix Finset Relation MeasureTheory

namespace SingleDoorConverse

/-- A coordinate hyperplane `{θ | θ i = 0}` of `ℝ^k` is a Lebesgue null set. -/
theorem volume_coord_eq_zero {k : ℕ} (i : Fin k) :
    volume {θ : Fin k → ℝ | θ i = 0} = 0 := by
  set s : Submodule ℝ (Fin k → ℝ) :=
    LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i)
  have h : {θ : Fin k → ℝ | θ i = 0} = (s : Set (Fin k → ℝ)) := by
    ext θ; simp [s]
  rw [h]
  refine Measure.addHaar_submodule _ _ fun htop => ?_
  have : (Pi.single i 1 : Fin k → ℝ) ∈ s := by
    rw [htop]; trivial
  simp [s] at this

/-! ### Pattern 1: a descendant of the outcome in the conditioning set -/

namespace Descendant

/-- The chain `X → Y → W` (`0 → 1 → 2`) with path coefficients `α` (of `X → Y`) and `β` (of
`Y → W`) and uncorrelated errors with variances `σx`, `σy`, `σw` (read as `max σ 0`, so that the
model is defined for every real parameter; the theorems assume positive variances). -/
noncomputable def model (α β σx σy σw : ℝ) : LinearSEM (Fin 3) where
  G := DescendantExample.G
  acyclic := by decide
  B := !![0, 0, 0; α, 0, 0; 0, β, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [DescendantExample.G]
  Ω := diagonal ![max σx 0, max σy 0, max σw 0]
  Ω_posSemidef := PosSemidef.diagonal fun i => by fin_cases i <;> simp

variable {α β σx σy σw : ℝ}

theorem T_eq : (model α β σx σy σw).T = !![1, 0, 0; α, 1, 0; α * β, β, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [model, Matrix.mul_apply, Fin.sum_univ_three]
    ring

/-- The entries of the implied covariance matrix that the regression uses. -/
theorem cov_vals (hx : 0 ≤ σx) (hy : 0 ≤ σy) (hw : 0 ≤ σw) :
    (model α β σx σy σw).cov 0 0 = σx ∧ (model α β σx σy σw).cov 0 1 = α * σx ∧
      (model α β σx σy σw).cov 0 2 = α * β * σx ∧
      (model α β σx σy σw).cov 2 1 = β * (α ^ 2 * σx + σy) ∧
      (model α β σx σy σw).cov 2 2 = β ^ 2 * (α ^ 2 * σx + σy) + σw := by
  simp only [cov_apply, T_eq]
  simp only [Fin.isValue, of_apply, cons_val', cons_val_fin_one, cons_val_zero, model,
    max_eq_left hx, max_eq_left hy, max_eq_left hw, Fin.sum_univ_three, mul_one, cons_val_one,
    mul_zero, add_zero, Matrix.cons_val, diagonal_apply_eq, one_mul, ne_eq, one_ne_zero,
    not_false_eq_true, diagonal_apply_ne, Fin.reduceEq, zero_ne_one, zero_mul, zero_add,
    add_left_inj, true_and]
  exact ⟨by ring, by ring, by ring, by ring⟩

/-- With positive error variances, the coefficient of `X` in the regression of `Y` on `X` and
`W` is `α σw / (β ^ 2 σy + σw)`. -/
theorem regCoeff_eq (hx : 0 < σx) (hy : 0 < σy) (hw : 0 < σw) :
    regCoeff (model α β σx σy σw).cov {0, 2} 1 0 = α * σw / (β ^ 2 * σy + σw) := by
  have hpd : (model α β σx σy σw).Ω.PosDef :=
    Matrix.posDef_diagonal_iff.2 fun i => by fin_cases i <;> simp [hx, hy, hw]
  have hu := isUnit_submatrix_of_posDef ((model α β σx σy σw).cov_posDef hpd) {0, 2}
  have hr := regCoeff_isRegCoeff 1 hu
  obtain ⟨h00, h01, h02, h21, h22⟩ := cov_vals (α := α) (β := β) hx.le hy.le hw.le
  have hpos : 0 < β ^ 2 * σy + σw := by positivity
  have hDe : (model α β σx σy σw).cov 0 0 * (model α β σx σy σw).cov 2 2 -
      (model α β σx σy σw).cov 0 2 ^ 2 = σx * (β ^ 2 * σy + σw) := by
    rw [h00, h22, h02]; ring
  have hD0 : σx * (β ^ 2 * σy + σw) ≠ 0 := by positivity
  rw [((isRegCoeff_pair_iff (by decide) ((model α β σx σy σw).cov_symm 2 0)
    (hDe ▸ hD0)).1 hr).2.1, hDe, h22, h01, h02, h21, div_eq_div_iff hD0 hpos.ne']
  ring

/-- With positive error variances every covariance block is invertible. -/
theorem isUnit_subCov (hx : 0 < σx) (hy : 0 < σy) (hw : 0 < σw) (S : Finset (Fin 3)) :
    IsUnit (subCov (model α β σx σy σw).cov S) :=
  isUnit_submatrix_of_posDef ((model α β σx σy σw).cov_posDef
    (Matrix.posDef_diagonal_iff.2 fun i => by fin_cases i <;> simp [hx, hy, hw])) S

/-- With positive error variances the regression coefficient equals the path coefficient
exactly when `α = 0` or `β = 0`. -/
theorem regCoeff_eq_B_iff (hx : 0 < σx) (hy : 0 < σy) (hw : 0 < σw) :
    regCoeff (model α β σx σy σw).cov {0, 2} 1 0 = (model α β σx σy σw).B 1 0 ↔
      α = 0 ∨ β = 0 := by
  have hpos : 0 < β ^ 2 * σy + σw := by positivity
  have hB : (model α β σx σy σw).B 1 0 = α := by simp [model]
  rw [regCoeff_eq hx hy hw, hB, div_eq_iff hpos.ne']
  constructor
  · intro h
    have h' : α * β ^ 2 * σy = 0 := by linarith
    rcases mul_eq_zero.1 h' with h'' | h''
    · rcases mul_eq_zero.1 h'' with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (pow_eq_zero_iff two_ne_zero |>.1 h3)
    · exact absurd h'' hy.ne'
  · rintro (rfl | rfl) <;> ring

/-- **Pattern 1 of the converse.** In the chain `X → Y → W` with `Z = {W}`, `X ∉ Z` and `Z`
d-separates `X` from `Y` after deleting `X → Y`, but `W` is a descendant of `Y`. The set of
parameters `(α, β, σx, σy, σw)` with positive variances at which the regression coefficient
`r_YX·W` equals the path coefficient `α` lies in `{α = 0} ∪ {β = 0}`, a Lebesgue null set
(`Descendant.witness` gives a point where they differ). -/
theorem exceptional_null :
    volume {θ : Fin 5 → ℝ | 0 < θ 2 ∧ 0 < θ 3 ∧ 0 < θ 4 ∧
      regCoeff (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4)).cov {0, 2} 1 0 =
        (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4)).B 1 0} = 0 := by
  refine measure_mono_null (t := {θ | θ 0 = 0} ∪ {θ | θ 1 = 0}) ?_
    (measure_union_null (volume_coord_eq_zero 0) (volume_coord_eq_zero 1))
  rintro θ ⟨h2, h3, h4, h⟩
  exact (regCoeff_eq_B_iff h2 h3 h4).1 h

/-- A parameter point of pattern 1 with invertible covariance blocks at which the regression
coefficient differs from the path coefficient: `α = β = 1` and unit variances give `1 / 2`
against `1`. -/
theorem witness :
    IsUnit (subCov (model 1 1 1 1 1).cov {2}) ∧ IsUnit (subCov (model 1 1 1 1 1).cov {0, 2}) ∧
      regCoeff (model 1 1 1 1 1).cov {0, 2} 1 0 = 1 / 2 ∧ (model 1 1 1 1 1).B 1 0 = 1 := by
  refine ⟨isUnit_subCov one_pos one_pos one_pos _, isUnit_subCov one_pos one_pos one_pos _, ?_,
    by simp [model]⟩
  rw [regCoeff_eq one_pos one_pos one_pos]; norm_num

/-- The graphical facts of pattern 1: `X → Y` is an edge, `X ∉ {W}`, `{W}` d-separates `X` from
`Y` in `G_α`, and `W` is a descendant of `Y`. -/
theorem graph_facts :
    (model α β σx σy σw).G.Adj 0 1 ∧ (0 : Fin 3) ∉ ({2} : Finset (Fin 3)) ∧
      (deleteEdgeGraph (model α β σx σy σw).G 0 1).DSep {0} {1} ↑({2} : Finset (Fin 3)) ∧
      ReflTransGen (model α β σx σy σw).G.Adj 1 2 :=
  ⟨Or.inl ⟨rfl, rfl⟩, by decide, DescendantExample.dSep_deleteEdgeGraph,
    ReflTransGen.single (Or.inr ⟨rfl, rfl⟩)⟩

end Descendant

/-! ### Pattern 2: an unblocked back-door path -/

namespace BackDoorPath

/-- The graph `C → X`, `C → Y`, `X → Y` with `C = 0`, `X = 1`, `Y = 2`. -/
def G : Digraph (Fin 3) where
  Adj i j := (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The confounded model `X = γ C + ε_X`, `Y = α X + δ C + ε_Y`, with uncorrelated errors of
variances `σc`, `σx`, `σy` (read as `max σ 0`). -/
noncomputable def model (γ δ α σc σx σy : ℝ) : LinearSEM (Fin 3) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0; γ, 0, 0; δ, α, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := diagonal ![max σc 0, max σx 0, max σy 0]
  Ω_posSemidef := PosSemidef.diagonal fun i => by fin_cases i <;> simp

variable {γ δ α σc σx σy : ℝ}

theorem T_eq : (model γ δ α σc σx σy).T = !![1, 0, 0; γ, 1, 0; δ + α * γ, α, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [model, Matrix.mul_apply, Fin.sum_univ_three]
    ring

theorem cov_vals (hc : 0 ≤ σc) (hx : 0 ≤ σx) (hy : 0 ≤ σy) :
    (model γ δ α σc σx σy).cov 1 1 = γ ^ 2 * σc + σx ∧
      (model γ δ α σc σx σy).cov 1 2 = γ * (δ + α * γ) * σc + α * σx := by
  simp only [cov_apply, T_eq]
  simp only [Fin.isValue, of_apply, cons_val', cons_val_fin_one, cons_val_one, cons_val_zero, model,
    max_eq_left hc, max_eq_left hx, max_eq_left hy, Fin.sum_univ_three, mul_one, Matrix.cons_val,
    mul_zero, add_zero, diagonal_apply_eq, ne_eq, zero_ne_one, not_false_eq_true,
    diagonal_apply_ne, one_ne_zero, zero_mul, one_mul, zero_add, Fin.reduceEq, add_left_inj]
  exact ⟨by ring, by ring⟩

/-- With positive error variances, the regression of `Y` on `X` alone (`Z = ∅`) has slope
`α + γ δ σc / (γ ^ 2 σc + σx)`. -/
theorem regCoeff_eq (hc : 0 < σc) (hx : 0 < σx) (hy : 0 < σy) :
    regCoeff (model γ δ α σc σx σy).cov {1} 2 1 = α + γ * δ * σc / (γ ^ 2 * σc + σx) := by
  have hpd : (model γ δ α σc σx σy).Ω.PosDef :=
    Matrix.posDef_diagonal_iff.2 fun i => by fin_cases i <;> simp [hc, hx, hy]
  have hu := isUnit_submatrix_of_posDef ((model γ δ α σc σx σy).cov_posDef hpd) {1}
  obtain ⟨h11, h12⟩ := cov_vals (γ := γ) (δ := δ) (α := α) hc.le hx.le hy.le
  have hpos : 0 < γ ^ 2 * σc + σx := by positivity
  have hxx : (model γ δ α σc σx σy).cov 1 1 ≠ 0 := by rw [h11]; exact hpos.ne'
  rw [(isRegCoeff_singleton_iff hxx).1 (regCoeff_isRegCoeff 2 hu), Pi.single_eq_same, h11, h12]
  field_simp
  ring

/-- With positive error variances every covariance block is invertible. -/
theorem isUnit_subCov (hc : 0 < σc) (hx : 0 < σx) (hy : 0 < σy) (S : Finset (Fin 3)) :
    IsUnit (subCov (model γ δ α σc σx σy).cov S) :=
  isUnit_submatrix_of_posDef ((model γ δ α σc σx σy).cov_posDef
    (Matrix.posDef_diagonal_iff.2 fun i => by fin_cases i <;> simp [hc, hx, hy])) S

/-- With positive error variances the regression slope equals the path coefficient exactly when
`γ = 0` or `δ = 0`. -/
theorem regCoeff_eq_B_iff (hc : 0 < σc) (hx : 0 < σx) (hy : 0 < σy) :
    regCoeff (model γ δ α σc σx σy).cov {1} 2 1 = (model γ δ α σc σx σy).B 2 1 ↔
      γ = 0 ∨ δ = 0 := by
  have hpos : 0 < γ ^ 2 * σc + σx := by positivity
  have hB : (model γ δ α σc σx σy).B 2 1 = α := by simp [model]
  rw [regCoeff_eq hc hx hy, hB, add_eq_left, div_eq_zero_iff, or_iff_left hpos.ne']
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h' | h'
    · exact (mul_eq_zero.1 h')
    · exact absurd h' hc.ne'
  · rintro (rfl | rfl) <;> ring

/-- **Pattern 2 of the converse.** In the graph `C → X`, `C → Y`, `X → Y` with `Z = ∅`, `Z`
contains no descendant of `Y` but does not d-separate `X` from `Y` after deleting `X → Y` (the
back-door path `X ← C → Y` is open). The set of parameters `(γ, δ, α, σc, σx, σy)` with positive
variances at which the regression slope equals the path coefficient `α` lies in
`{γ = 0} ∪ {δ = 0}`, a Lebesgue null set. -/
theorem exceptional_null :
    volume {θ : Fin 6 → ℝ | 0 < θ 3 ∧ 0 < θ 4 ∧ 0 < θ 5 ∧
      regCoeff (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5)).cov {1} 2 1 =
        (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5)).B 2 1} = 0 := by
  refine measure_mono_null (t := {θ | θ 0 = 0} ∪ {θ | θ 1 = 0}) ?_
    (measure_union_null (volume_coord_eq_zero 0) (volume_coord_eq_zero 1))
  rintro θ ⟨h3, h4, h5, h⟩
  exact (regCoeff_eq_B_iff h3 h4 h5).1 h

/-- A parameter point of pattern 2 with invertible covariance blocks at which the regression
slope differs from the path coefficient: all coefficients and variances `1` give `3 / 2` against
`1`. -/
theorem witness :
    IsUnit (subCov (model 1 1 1 1 1 1).cov ∅) ∧ IsUnit (subCov (model 1 1 1 1 1 1).cov {1}) ∧
      regCoeff (model 1 1 1 1 1 1).cov {1} 2 1 = 3 / 2 ∧ (model 1 1 1 1 1 1).B 2 1 = 1 := by
  refine ⟨isUnit_subCov one_pos one_pos one_pos _, isUnit_subCov one_pos one_pos one_pos _, ?_,
    by simp [model]⟩
  rw [regCoeff_eq one_pos one_pos one_pos]; norm_num

/-- The graphical facts of pattern 2: `X → Y` is an edge and `∅` does not d-separate `X` from `Y`
in `G_α`. -/
theorem graph_facts :
    (model γ δ α σc σx σy).G.Adj 1 2 ∧
      ¬ (deleteEdgeGraph (model γ δ α σc σx σy).G 1 2).DSep {1} {2} ↑(∅ : Finset (Fin 3)) := by
  refine ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), fun hsep => hsep ⟨1, rfl, 2, rfl, by simp, by simp, true,
    ReflTransGen.head (b := (0, false)) ?_ (ReflTransGen.single ?_)⟩⟩
  · exact Digraph.bayesBall_adj_false_false.2 ⟨⟨Or.inl ⟨rfl, rfl⟩, by decide⟩, by simp⟩
  · exact Digraph.bayesBall_adj_true.2 ⟨⟨Or.inr (Or.inl ⟨rfl, rfl⟩), by decide⟩, by simp⟩

end BackDoorPath

/-! ### Pattern 3: a collider opened by the conditioning set -/

namespace Collider

/-- The graph `X → C ← U → Y`, `X → Y` with `X = 0`, `U = 1`, `C = 2`, `Y = 3`. -/
def G : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The model `C = a X + b U + ε_C`, `Y = α X + d U + ε_Y`, with `X`, `U` exogenous and
uncorrelated errors of variances `σx`, `σu`, `σc`, `σy` (read as `max σ 0`). -/
noncomputable def model (a b α d σx σu σc σy : ℝ) : LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; 0, 0, 0, 0; a, b, 0, 0; α, d, 0, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := diagonal ![max σx 0, max σu 0, max σc 0, max σy 0]
  Ω_posSemidef := PosSemidef.diagonal fun i => by fin_cases i <;> simp

variable {a b α d σx σu σc σy : ℝ}

theorem T_eq : (model a b α d σx σu σc σy).T = !![1, 0, 0, 0; 0, 1, 0, 0; a, b, 1, 0; α, d, 0, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [model, Matrix.mul_apply, Fin.sum_univ_four]

theorem cov_vals (hx : 0 ≤ σx) (hu : 0 ≤ σu) (hc : 0 ≤ σc) (hy : 0 ≤ σy) :
    (model a b α d σx σu σc σy).cov 0 0 = σx ∧ (model a b α d σx σu σc σy).cov 0 2 = a * σx ∧
      (model a b α d σx σu σc σy).cov 0 3 = α * σx ∧
      (model a b α d σx σu σc σy).cov 2 2 = a ^ 2 * σx + b ^ 2 * σu + σc ∧
      (model a b α d σx σu σc σy).cov 2 3 = a * α * σx + b * d * σu := by
  simp only [cov_apply, T_eq]
  simp only [Fin.isValue, of_apply, cons_val', cons_val_fin_one, cons_val_zero, model,
    max_eq_left hx, max_eq_left hu, max_eq_left hc, max_eq_left hy, Fin.sum_univ_four, mul_one,
    cons_val_one, mul_zero, add_zero, Matrix.cons_val, diagonal_apply_eq, one_mul, ne_eq,
    one_ne_zero, not_false_eq_true, diagonal_apply_ne, Fin.reduceEq, zero_ne_one, zero_mul,
    zero_add, add_left_inj, true_and]
  exact ⟨by ring, by ring, by ring, by ring⟩

/-- With positive error variances, the coefficient of `X` in the regression of `Y` on `X` and
`C` is `α - a b d σu / (b ^ 2 σu + σc)`. -/
theorem regCoeff_eq (hx : 0 < σx) (hu : 0 < σu) (hc : 0 < σc) (hy : 0 < σy) :
    regCoeff (model a b α d σx σu σc σy).cov {0, 2} 3 0 =
      α - a * b * d * σu / (b ^ 2 * σu + σc) := by
  have hpd : (model a b α d σx σu σc σy).Ω.PosDef :=
    Matrix.posDef_diagonal_iff.2 fun i => by fin_cases i <;> simp [hx, hu, hc, hy]
  have hU := isUnit_submatrix_of_posDef ((model a b α d σx σu σc σy).cov_posDef hpd) {0, 2}
  have hr := regCoeff_isRegCoeff 3 hU
  obtain ⟨h00, h02, h03, h22, h23⟩ :=
    cov_vals (a := a) (b := b) (α := α) (d := d) hx.le hu.le hc.le hy.le
  have hpos : 0 < b ^ 2 * σu + σc := by positivity
  have hDe : (model a b α d σx σu σc σy).cov 0 0 * (model a b α d σx σu σc σy).cov 2 2 -
      (model a b α d σx σu σc σy).cov 0 2 ^ 2 = σx * (b ^ 2 * σu + σc) := by
    rw [h00, h22, h02]; ring
  have hD0 : σx * (b ^ 2 * σu + σc) ≠ 0 := by positivity
  rw [((isRegCoeff_pair_iff (by decide) ((model a b α d σx σu σc σy).cov_symm 2 0)
    (hDe ▸ hD0)).1 hr).2.1, hDe, h22, h03, h02, h23]
  field_simp
  ring

/-- With positive error variances every covariance block is invertible. -/
theorem isUnit_subCov (hx : 0 < σx) (hu : 0 < σu) (hc : 0 < σc) (hy : 0 < σy)
    (S : Finset (Fin 4)) : IsUnit (subCov (model a b α d σx σu σc σy).cov S) :=
  isUnit_submatrix_of_posDef ((model a b α d σx σu σc σy).cov_posDef
    (Matrix.posDef_diagonal_iff.2 fun i => by fin_cases i <;> simp [hx, hu, hc, hy])) S

/-- With positive error variances the regression coefficient equals the path coefficient
exactly when `a = 0`, `b = 0` or `d = 0`. -/
theorem regCoeff_eq_B_iff (hx : 0 < σx) (hu : 0 < σu) (hc : 0 < σc) (hy : 0 < σy) :
    regCoeff (model a b α d σx σu σc σy).cov {0, 2} 3 0 = (model a b α d σx σu σc σy).B 3 0 ↔
      a = 0 ∨ b = 0 ∨ d = 0 := by
  have hpos : 0 < b ^ 2 * σu + σc := by positivity
  have hB : (model a b α d σx σu σc σy).B 3 0 = α := by simp [model]
  rw [regCoeff_eq hx hu hc hy, hB, sub_eq_self, div_eq_zero_iff, or_iff_left hpos.ne']
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · rcases mul_eq_zero.1 h'' with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr h'')
    · exact absurd h' hu.ne'
  · rintro (rfl | rfl | rfl) <;> ring

/-- **Pattern 3 of the converse.** In the graph `X → C ← U → Y`, `X → Y` with `Z = {C}`, `C` is
not a descendant of `Y`, but conditioning on the collider `C` opens the path `X → C ← U → Y`,
so `Z` does not d-separate `X` from `Y` after deleting `X → Y`. The set of parameters
`(a, b, α, d, σx, σu, σc, σy)` with positive variances at which `r_YX·C` equals the path
coefficient `α` lies in `{a = 0} ∪ {b = 0} ∪ {d = 0}`, a Lebesgue null set. -/
theorem exceptional_null :
    volume {θ : Fin 8 → ℝ | 0 < θ 4 ∧ 0 < θ 5 ∧ 0 < θ 6 ∧ 0 < θ 7 ∧
      regCoeff (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6) (θ 7)).cov {0, 2} 3 0 =
        (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6) (θ 7)).B 3 0} = 0 := by
  refine measure_mono_null (t := {θ | θ 0 = 0} ∪ ({θ | θ 1 = 0} ∪ {θ | θ 3 = 0})) ?_
    (measure_union_null (volume_coord_eq_zero 0)
      (measure_union_null (volume_coord_eq_zero 1) (volume_coord_eq_zero 3)))
  rintro θ ⟨h4, h5, h6, h7, h⟩
  exact (regCoeff_eq_B_iff h4 h5 h6 h7).1 h

/-- A parameter point of pattern 3 with invertible covariance blocks at which the regression
coefficient differs from the path coefficient: all coefficients and variances `1` give `1 / 2`
against `1`. -/
theorem witness :
    IsUnit (subCov (model 1 1 1 1 1 1 1 1).cov {2}) ∧
      IsUnit (subCov (model 1 1 1 1 1 1 1 1).cov {0, 2}) ∧
      regCoeff (model 1 1 1 1 1 1 1 1).cov {0, 2} 3 0 = 1 / 2 ∧
      (model 1 1 1 1 1 1 1 1).B 3 0 = 1 := by
  refine ⟨isUnit_subCov one_pos one_pos one_pos one_pos _,
    isUnit_subCov one_pos one_pos one_pos one_pos _, ?_, by simp [model]⟩
  rw [regCoeff_eq one_pos one_pos one_pos one_pos]; norm_num

/-- The graphical facts of pattern 3: `X → Y` is an edge, `X ∉ {C}`, `C` is not a descendant of
`Y`, and `{C}` does not d-separate `X` from `Y` in `G_α`. -/
theorem graph_facts :
    (model a b α d σx σu σc σy).G.Adj 0 3 ∧ (0 : Fin 4) ∉ ({2} : Finset (Fin 4)) ∧
      ¬ ReflTransGen (model a b α d σx σu σc σy).G.Adj 3 2 ∧
      ¬ (deleteEdgeGraph (model a b α d σx σu σc σy).G 0 3).DSep {0} {3}
        ↑({2} : Finset (Fin 4)) := by
  refine ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), by decide, fun h => ?_, fun hsep => ?_⟩
  · rcases ReflTransGen.cases_head h with h | ⟨w, hw, -⟩
    · exact absurd h (by decide)
    · simp [model, G] at hw
  · refine hsep ⟨0, rfl, 3, rfl, by simp, by simp, true,
      ReflTransGen.head (b := (2, true)) ?_
        (ReflTransGen.head (b := (1, false)) ?_ (ReflTransGen.single ?_))⟩
    · exact Digraph.bayesBall_adj_true.2 ⟨⟨Or.inl ⟨rfl, rfl⟩, by decide⟩, by simp⟩
    · exact Digraph.bayesBall_adj_true_false.2 ⟨⟨Or.inr (Or.inl ⟨rfl, rfl⟩), by decide⟩,
        Digraph.subset_ancestorsOf _ (by simp)⟩
    · exact Digraph.bayesBall_adj_true.2 ⟨⟨Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), by decide⟩,
        by simp⟩

end Collider

end SingleDoorConverse

end LinearSEM

end CausalInference
