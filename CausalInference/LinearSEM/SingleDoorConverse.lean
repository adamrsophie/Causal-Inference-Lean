/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.DSeparation
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import CausalInference.Basic.PolynomialNullSet

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
fails and which hold. `exceptional_null_of_polynomial` derives the same null statement from the
fact that the zero set of a nonzero polynomial is null (`volume_zeroSet_eq_zero`), applied to
the numerator of the bias.

## Failure patterns on an arbitrary graph

For an arbitrary acyclic graph `G` with an edge `x → y` and a set `Z` containing neither `x`
nor any descendant of `y`, `exists_ne_of_fork`, `exists_ne_of_chain` and `exists_ne_of_collider`
give a linear SEM on `G` with uncorrelated unit-variance errors (so every covariance block is
invertible) at which the coefficient of `x` in the regression of `y` on `x` and `Z` differs from
the path coefficient, whenever `Z` leaves open a path of `G` with `x → y` deleted of one of the
shapes `x ← m → y` or `x → m → y` (with `m ∉ Z`), or `x → c ← w → y` (with `c ∈ Z`, `w ∉ Z`).
The model has coefficient `1` on the edges of the pattern and `0` on every other edge of `G`;
the other variables are then uncorrelated with the pattern, and regressors uncorrelated with the
outcome and with the other regressors do not change a regression
(`isRegCoeff_of_uncorrelated`).

The general case is proved in `CausalInference.LinearSEM.SingleDoorGeneric` and
`CausalInference.LinearSEM.SingleDoorTrail`: the bias times the regression determinant is a
polynomial in all parameters (`SingleDoorGeneric.biasPoly`), it is not the zero polynomial when
the single-door condition fails (a witness is built from a minimal d-connecting trail of any
length, or from a directed path from `y` to `Z`), and so the exceptional set is null on every
acyclic graph (`SingleDoorGeneric.volume_exceptional_eq_zero_of_not_singleDoor`).

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

/-- The exceptional set of pattern 1 lies in the zero set of the nonzero polynomial
`α β ^ 2 σy`, the numerator of the bias `r_YX·W - α = -α β ^ 2 σy / (β ^ 2 σy + σw)`; it is
therefore null by `volume_zeroSet_eq_zero`. -/
theorem exceptional_null_of_polynomial :
    volume {θ : Fin 5 → ℝ | 0 < θ 2 ∧ 0 < θ 3 ∧ 0 < θ 4 ∧
      regCoeff (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4)).cov {0, 2} 1 0 =
        (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4)).B 1 0} = 0 := by
  have hP : (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 * MvPolynomial.X 3 :
      MvPolynomial (Fin 5) ℝ) ≠ 0 := fun h => by
    simpa using congrArg (MvPolynomial.eval fun _ => (1 : ℝ)) h
  refine measure_mono_null ?_ (volume_zeroSet_eq_zero hP)
  rintro θ ⟨h2, h3, h4, h⟩
  rcases (regCoeff_eq_B_iff h2 h3 h4).1 h with h0 | h0 <;> simp [h0]

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

/-- The exceptional set of pattern 2 lies in the zero set of the nonzero polynomial `γ δ σc`,
the numerator of the bias `γ δ σc / (γ ^ 2 σc + σx)`; it is therefore null by
`volume_zeroSet_eq_zero`. -/
theorem exceptional_null_of_polynomial :
    volume {θ : Fin 6 → ℝ | 0 < θ 3 ∧ 0 < θ 4 ∧ 0 < θ 5 ∧
      regCoeff (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5)).cov {1} 2 1 =
        (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5)).B 2 1} = 0 := by
  have hP : (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 :
      MvPolynomial (Fin 6) ℝ) ≠ 0 := fun h => by
    simpa using congrArg (MvPolynomial.eval fun _ => (1 : ℝ)) h
  refine measure_mono_null ?_ (volume_zeroSet_eq_zero hP)
  rintro θ ⟨h3, h4, h5, h⟩
  rcases (regCoeff_eq_B_iff h3 h4 h5).1 h with h0 | h0 <;> simp [h0]

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

/-- The exceptional set of pattern 3 lies in the zero set of the nonzero polynomial `a b d σu`,
the numerator of the bias `-a b d σu / (b ^ 2 σu + σc)`; it is therefore null by
`volume_zeroSet_eq_zero`. -/
theorem exceptional_null_of_polynomial :
    volume {θ : Fin 8 → ℝ | 0 < θ 4 ∧ 0 < θ 5 ∧ 0 < θ 6 ∧ 0 < θ 7 ∧
      regCoeff (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6) (θ 7)).cov {0, 2} 3 0 =
        (model (θ 0) (θ 1) (θ 2) (θ 3) (θ 4) (θ 5) (θ 6) (θ 7)).B 3 0} = 0 := by
  have hP : (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 * MvPolynomial.X 5 :
      MvPolynomial (Fin 8) ℝ) ≠ 0 := fun h => by
    simpa using congrArg (MvPolynomial.eval fun _ => (1 : ℝ)) h
  refine measure_mono_null ?_ (volume_zeroSet_eq_zero hP)
  rintro θ ⟨h4, h5, h6, h7, h⟩
  rcases (regCoeff_eq_B_iff h4 h5 h6 h7).1 h with h0 | h0 | h0 <;> simp [h0]

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

/-! ### Failure patterns on an arbitrary graph -/

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Adding regressors that are uncorrelated with the outcome and with the other regressors does
not change the regression coefficients. -/
theorem isRegCoeff_of_uncorrelated {C : Matrix V V ℝ} {S₁ S : Finset V} {y : V} {β : V → ℝ}
    (h : IsRegCoeff C S₁ y β) (hS : S₁ ⊆ S)
    (hC : ∀ s ∈ S, s ∉ S₁ → C s y = 0 ∧ ∀ t ∈ S₁, C s t = 0) : IsRegCoeff C S y β := by
  refine ⟨fun v hv => h.1 v fun h' => hv (hS h'), fun s hs => ?_⟩
  by_cases hs₁ : s ∈ S₁
  · exact h.2 s hs₁
  · rw [(hC s hs hs₁).1]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t ∈ S₁
    · rw [(hC s hs hs₁).2 t ht, zero_mul]
    · rw [h.1 t ht, mul_zero]

omit [Fintype V] [DecidableEq V] in
/-- A set closed under taking parents contains every ancestor of its members. -/
theorem mem_of_reflTransGen {H : Digraph V} {S : Set V}
    (hS : ∀ u w, H.Adj u w → w ∈ S → u ∈ S) {a v : V} (h : ReflTransGen H.Adj a v)
    (hv : v ∈ S) : a ∈ S := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hab _ ih => exact hS _ _ hab ih

omit [Fintype V] [DecidableEq V] in
theorem ne_of_adj_of_isAcyclic {G : Digraph V} (hG : G.IsAcyclic) {u v : V} (h : G.Adj u v) :
    u ≠ v := by
  rintro rfl
  exact hG u (TransGen.single h)

omit [DecidableEq V] in
theorem sum_eq_sum_of_support {f : V → ℝ} (s : Finset V) (h : ∀ a, a ∉ s → f a = 0) :
    ∑ a, f a = ∑ a ∈ s, f a :=
  (Finset.sum_subset (Finset.subset_univ s) fun a _ ha => h a ha).symm

theorem T_apply_rec (M : LinearSEM V) (v u : V) :
    M.T v u = (if v = u then 1 else 0) + ∑ k, M.B v k * M.T k u := by
  conv_lhs => rw [M.T_eq_one_add_B_mul_T]
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply]

theorem cov_apply_of_eq_one (M : LinearSEM V) (hΩ : M.Ω = 1) (v w : V) :
    M.cov v w = ∑ a, M.T v a * M.T w a := by
  rw [M.cov_apply_of_isDiag (hΩ ▸ isDiag_one)]
  simp [hΩ]

/-- The model on an acyclic graph `H` with coefficient `1` on every edge and uncorrelated
errors of variance `1`. -/
noncomputable def unitModel (H : Digraph V) [DecidableRel H.Adj] (hH : H.IsAcyclic) :
    LinearSEM V where
  G := H
  acyclic := hH
  B v u := if H.Adj u v then 1 else 0
  B_support v u h := by
    by_contra h'
    simp [h'] at h
  Ω := 1
  Ω_posSemidef := PosSemidef.one

/-- The same coefficients and errors, read on a larger acyclic graph `G`. -/
def onGraph (M : LinearSEM V) (G : Digraph V) (hG : G.IsAcyclic)
    (hle : ∀ u v, M.G.Adj u v → G.Adj u v) : LinearSEM V where
  G := G
  acyclic := hG
  B := M.B
  B_support v u h := hle _ _ (M.B_support v u h)
  Ω := M.Ω
  Ω_posSemidef := M.Ω_posSemidef

/-! #### An open fork `x ← m → y` -/

/-- The fork pattern: edges `m → x`, `m → y`, `x → y`. -/
def forkGraph (x y m : V) : Digraph V where
  Adj p q := (p = m ∧ q = x) ∨ (p = m ∧ q = y) ∨ (p = x ∧ q = y)

instance (x y m : V) : DecidableRel (forkGraph x y m).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- In a model whose only edges are `m → x`, `m → y`, `x → y`, all with coefficient `1`, and
whose errors are uncorrelated with variance `1`, the coefficient of `x` in the regression of `y`
on `x` and any set `Z` avoiding `x`, `y`, `m` is `3 / 2`. -/
theorem fork_regCoeff (M : LinearSEM V) (hΩ : M.Ω = 1) {x y m : V}
    (hB : ∀ v u, M.B v u = if (u = m ∧ v = x) ∨ (u = m ∧ v = y) ∨ (u = x ∧ v = y) then 1 else 0)
    (hE : ∀ p q, M.G.Adj p q → (p = m ∧ q = x) ∨ (p = m ∧ q = y) ∨ (p = x ∧ q = y))
    (nxy : x ≠ y) (nmx : m ≠ x) (nmy : m ≠ y) {Z : Finset V} (hxZ : x ∉ Z) (hyZ : y ∉ Z)
    (hmZ : m ∉ Z) : regCoeff M.cov (insert x Z) y x = 3 / 2 := by
  have anc_m : ∀ a, ReflTransGen M.G.Adj a m → a = m := fun a h =>
    mem_of_reflTransGen (S := {m}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h rfl
  have anc_x : ∀ a, ReflTransGen M.G.Adj a x → a = x ∨ a = m := fun a h =>
    mem_of_reflTransGen (S := {x, m}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h (by simp)
  have anc_y : ∀ a, ReflTransGen M.G.Adj a y → a = y ∨ a = x ∨ a = m := fun a h =>
    mem_of_reflTransGen (S := {y, x, m}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h (by simp)
  have anc_s : ∀ s, s ≠ x → s ≠ y → ∀ a, ReflTransGen M.G.Adj a s → a = s := fun s hsx hsy a h =>
    mem_of_reflTransGen (S := {s}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h rfl
  have hBx : ∀ k, M.B x k = if k = m then 1 else 0 := fun k => by
    rw [hB]; by_cases hk : k = m <;> simp [hk, nxy]
  have hBy : ∀ k, M.B y k = if k = m ∨ k = x then 1 else 0 := fun k => by
    rw [hB]; by_cases hk : k = m <;> by_cases hk' : k = x <;> simp [hk, hk', Ne.symm nxy]
  have sum_x : ∀ u, ∑ k, M.B x k * M.T k u = M.T m u := fun u => by
    rw [sum_eq_sum_of_support {m} fun k hk => by simp [hBx, show k ≠ m by simpa using hk]]
    simp [hBx]
  have sum_y : ∀ u, ∑ k, M.B y k * M.T k u = M.T m u + M.T x u := fun u => by
    rw [sum_eq_sum_of_support {m, x} fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [hBy, hk.1, hk.2], Finset.sum_pair nmx]
    simp [hBy]
  have Tmx : M.T m x = 0 := M.T_apply_eq_zero fun h => nmx (anc_m x h).symm
  have Txm : M.T x m = 1 := by
    rw [T_apply_rec, sum_x, M.T_apply_self]; norm_num [Ne.symm nmx]
  have Tyx : M.T y x = 1 := by
    rw [T_apply_rec, sum_y, Tmx, M.T_apply_self]; norm_num [Ne.symm nxy]
  have Tym : M.T y m = 2 := by
    rw [T_apply_rec, sum_y, Txm, M.T_apply_self]; norm_num [Ne.symm nmy]
  have Tx0 : ∀ a, a ≠ x → a ≠ m → M.T x a = 0 := fun a h1 h2 =>
    M.T_apply_eq_zero fun h => (anc_x a h).elim h1 h2
  have Cxx : M.cov x x = 2 := by
    rw [cov_apply_of_eq_one M hΩ, sum_eq_sum_of_support {x, m} fun a ha => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [Tx0 a ha.1 ha.2], Finset.sum_pair (Ne.symm nmx), M.T_apply_self, Txm]
    norm_num
  have Cxy : M.cov x y = 3 := by
    rw [cov_apply_of_eq_one M hΩ, sum_eq_sum_of_support {x, m} fun a ha => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [Tx0 a ha.1 ha.2], Finset.sum_pair (Ne.symm nmx), M.T_apply_self, Txm, Tyx, Tym]
    norm_num
  have Cs : ∀ s, s ≠ x → s ≠ y → s ≠ m → ∀ w, (w = x ∨ w = y) → M.cov s w = 0 := by
    intro s hsx hsy hsm w hw
    rw [cov_apply_of_eq_one M hΩ, sum_eq_sum_of_support {s} fun a ha => by
      have : M.T s a = 0 := M.T_apply_eq_zero fun h =>
        (by simpa using ha : a ≠ s) (anc_s s hsx hsy a h)
      simp [this], Finset.sum_singleton, M.T_apply_self, one_mul]
    refine M.T_apply_eq_zero fun h => ?_
    rcases hw with rfl | rfl
    · exact (anc_x s h).elim hsx hsm
    · exact (anc_y s h).elim hsy fun h' => h'.elim hsx hsm
  have hβ : IsRegCoeff M.cov (insert x Z) y (Pi.single x (M.cov x y / M.cov x x)) := by
    refine isRegCoeff_of_uncorrelated ((isRegCoeff_singleton_iff (by rw [Cxx]; norm_num)).2 rfl)
      (by simp) fun s hs hs₁ => ?_
    have hsx : s ≠ x := by simpa using hs₁
    have hsZ : s ∈ Z := (Finset.mem_insert.1 hs).resolve_left hsx
    have hsy : s ≠ y := fun h => hyZ (h ▸ hsZ)
    have hsm : s ≠ m := fun h => hmZ (h ▸ hsZ)
    exact ⟨Cs s hsx hsy hsm y (Or.inr rfl), fun t ht => by
      rw [Finset.mem_singleton.1 ht]; exact Cs s hsx hsy hsm x (Or.inl rfl)⟩
  have hu : IsUnit (subCov M.cov (insert x Z)) :=
    isUnit_submatrix_of_posDef (M.cov_posDef (hΩ ▸ PosDef.one)) _
  rw [(regCoeff_isRegCoeff y hu).unique hu hβ, Pi.single_eq_same, Cxx, Cxy]

/-- **An open fork on an arbitrary graph.** Let `G` be acyclic with edges `x → y`, `m → x` and
`m → y`, and let `Z` contain neither `x` nor `m` nor any descendant of `y`. Then the fork
`x ← m → y` is an open path of `G` with `x → y` deleted, and there is a linear SEM on `G` with
uncorrelated unit-variance errors (so every covariance block is invertible) at which the
coefficient of `x` in the regression of `y` on `x` and `Z` differs from the path coefficient. -/
theorem exists_ne_of_fork {G : Digraph V} (hG : G.IsAcyclic) {x y m : V} {Z : Finset V}
    (hxy : G.Adj x y) (hmx : G.Adj m x) (hmy : G.Adj m y) (hxZ : x ∉ Z) (hmZ : m ∉ Z)
    (hZ : ∀ s ∈ Z, ¬ ReflTransGen G.Adj y s) :
    ∃ M : LinearSEM V, M.G = G ∧ M.Ω = 1 ∧ (∀ S : Finset V, IsUnit (subCov M.cov S)) ∧
      regCoeff M.cov (insert x Z) y x ≠ M.B y x := by
  have hyZ : y ∉ Z := fun h => hZ y h ReflTransGen.refl
  have hle : ∀ p q, (forkGraph x y m).Adj p q → G.Adj p q := by
    intro p q h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> assumption
  have hH : (forkGraph x y m).IsAcyclic := Digraph.IsAcyclic.anti (H := forkGraph x y m) hle hG
  let M₀ := unitModel (forkGraph x y m) hH
  have h32 : regCoeff M₀.cov (insert x Z) y x = 3 / 2 :=
    fork_regCoeff M₀ rfl (fun _ _ => rfl) (fun _ _ h => h) (ne_of_adj_of_isAcyclic hG hxy)
      (ne_of_adj_of_isAcyclic hG hmx) (ne_of_adj_of_isAcyclic hG hmy) hxZ hyZ hmZ
  refine ⟨onGraph M₀ G hG hle, rfl, rfl, fun S =>
    isUnit_submatrix_of_posDef (M₀.cov_posDef PosDef.one) S, ?_⟩
  change regCoeff M₀.cov (insert x Z) y x ≠ M₀.B y x
  rw [h32]
  simp [M₀, unitModel, forkGraph]
  norm_num

/-! #### An open chain `x → m → y` -/

/-- The chain pattern: edges `x → m`, `m → y`, `x → y`. -/
def chainGraph (x y m : V) : Digraph V where
  Adj p q := (p = x ∧ q = m) ∨ (p = m ∧ q = y) ∨ (p = x ∧ q = y)

instance (x y m : V) : DecidableRel (chainGraph x y m).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- In a model whose only edges are `x → m`, `m → y`, `x → y`, all with coefficient `1`, and
whose errors are uncorrelated with variance `1`, the coefficient of `x` in the regression of `y`
on `x` and any set `Z` avoiding `x`, `y`, `m` is the total effect `2`. -/
theorem chain_regCoeff (M : LinearSEM V) (hΩ : M.Ω = 1) {x y m : V}
    (hB : ∀ v u, M.B v u = if (u = x ∧ v = m) ∨ (u = m ∧ v = y) ∨ (u = x ∧ v = y) then 1 else 0)
    (hE : ∀ p q, M.G.Adj p q → (p = x ∧ q = m) ∨ (p = m ∧ q = y) ∨ (p = x ∧ q = y))
    (nxy : x ≠ y) (nxm : x ≠ m) (nmy : m ≠ y) {Z : Finset V} (hxZ : x ∉ Z) (hyZ : y ∉ Z)
    (hmZ : m ∉ Z) : regCoeff M.cov (insert x Z) y x = 2 := by
  have anc_x : ∀ a, ReflTransGen M.G.Adj a x → a = x := fun a h =>
    mem_of_reflTransGen (S := {x}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h rfl
  have anc_y : ∀ a, ReflTransGen M.G.Adj a y → a = y ∨ a = m ∨ a = x := fun a h =>
    mem_of_reflTransGen (S := {y, m, x}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h (by simp)
  have anc_s : ∀ s, s ≠ m → s ≠ y → ∀ a, ReflTransGen M.G.Adj a s → a = s :=
    fun s hsm hsy a h => mem_of_reflTransGen (S := {s}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h rfl
  have hBm : ∀ k, M.B m k = if k = x then 1 else 0 := fun k => by
    rw [hB]; by_cases hk : k = x <;> simp [hk, nmy]
  have hBy : ∀ k, M.B y k = if k = m ∨ k = x then 1 else 0 := fun k => by
    rw [hB]; by_cases hk : k = m <;> by_cases hk' : k = x <;> simp [hk, hk', Ne.symm nmy]
  have sum_m : ∀ u, ∑ k, M.B m k * M.T k u = M.T x u := fun u => by
    rw [sum_eq_sum_of_support {x} fun k hk => by simp [hBm, show k ≠ x by simpa using hk]]
    simp [hBm]
  have sum_y : ∀ u, ∑ k, M.B y k * M.T k u = M.T m u + M.T x u := fun u => by
    rw [sum_eq_sum_of_support {m, x} fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [hBy, hk.1, hk.2], Finset.sum_pair (Ne.symm nxm)]
    simp [hBy]
  have Tmx : M.T m x = 1 := by
    rw [T_apply_rec, sum_m, M.T_apply_self]; norm_num [Ne.symm nxm]
  have Tyx : M.T y x = 2 := by
    rw [T_apply_rec, sum_y, Tmx, M.T_apply_self]; norm_num [Ne.symm nxy]
  have Tx0 : ∀ a, a ≠ x → M.T x a = 0 := fun a h1 =>
    M.T_apply_eq_zero fun h => h1 (anc_x a h)
  have Cxx : M.cov x x = 1 := by
    rw [cov_apply_of_eq_one M hΩ, sum_eq_sum_of_support {x} fun a ha => by
      simp [Tx0 a (by simpa using ha)], Finset.sum_singleton, M.T_apply_self]
    norm_num
  have Cxy : M.cov x y = 2 := by
    rw [cov_apply_of_eq_one M hΩ, sum_eq_sum_of_support {x} fun a ha => by
      simp [Tx0 a (by simpa using ha)], Finset.sum_singleton, M.T_apply_self, Tyx]
    norm_num
  have Cs : ∀ s, s ≠ x → s ≠ y → s ≠ m → ∀ w, (w = x ∨ w = y) → M.cov s w = 0 := by
    intro s hsx hsy hsm w hw
    rw [cov_apply_of_eq_one M hΩ, sum_eq_sum_of_support {s} fun a ha => by
      have : M.T s a = 0 := M.T_apply_eq_zero fun h =>
        (by simpa using ha : a ≠ s) (anc_s s hsm hsy a h)
      simp [this], Finset.sum_singleton, M.T_apply_self, one_mul]
    refine M.T_apply_eq_zero fun h => ?_
    rcases hw with rfl | rfl
    · exact hsx (anc_x s h)
    · exact (anc_y s h).elim hsy fun h' => h'.elim hsm hsx
  have hβ : IsRegCoeff M.cov (insert x Z) y (Pi.single x (M.cov x y / M.cov x x)) := by
    refine isRegCoeff_of_uncorrelated ((isRegCoeff_singleton_iff (by rw [Cxx]; norm_num)).2 rfl)
      (by simp) fun s hs hs₁ => ?_
    have hsx : s ≠ x := by simpa using hs₁
    have hsZ : s ∈ Z := (Finset.mem_insert.1 hs).resolve_left hsx
    have hsy : s ≠ y := fun h => hyZ (h ▸ hsZ)
    have hsm : s ≠ m := fun h => hmZ (h ▸ hsZ)
    exact ⟨Cs s hsx hsy hsm y (Or.inr rfl), fun t ht => by
      rw [Finset.mem_singleton.1 ht]; exact Cs s hsx hsy hsm x (Or.inl rfl)⟩
  have hu : IsUnit (subCov M.cov (insert x Z)) :=
    isUnit_submatrix_of_posDef (M.cov_posDef (hΩ ▸ PosDef.one)) _
  rw [(regCoeff_isRegCoeff y hu).unique hu hβ, Pi.single_eq_same, Cxx, Cxy]
  norm_num

/-- **An open chain on an arbitrary graph.** Let `G` be acyclic with edges `x → y`, `x → m` and
`m → y`, and let `Z` contain neither `x` nor `m` nor any descendant of `y`. Then the chain
`x → m → y` is an open path of `G` with `x → y` deleted, and there is a linear SEM on `G` with
uncorrelated unit-variance errors at which the coefficient of `x` in the regression of `y` on `x`
and `Z` differs from the path coefficient. -/
theorem exists_ne_of_chain {G : Digraph V} (hG : G.IsAcyclic) {x y m : V} {Z : Finset V}
    (hxy : G.Adj x y) (hxm : G.Adj x m) (hmy : G.Adj m y) (hxZ : x ∉ Z) (hmZ : m ∉ Z)
    (hZ : ∀ s ∈ Z, ¬ ReflTransGen G.Adj y s) :
    ∃ M : LinearSEM V, M.G = G ∧ M.Ω = 1 ∧ (∀ S : Finset V, IsUnit (subCov M.cov S)) ∧
      regCoeff M.cov (insert x Z) y x ≠ M.B y x := by
  have hyZ : y ∉ Z := fun h => hZ y h ReflTransGen.refl
  have hle : ∀ p q, (chainGraph x y m).Adj p q → G.Adj p q := by
    intro p q h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> assumption
  have hH : (chainGraph x y m).IsAcyclic :=
    Digraph.IsAcyclic.anti (H := chainGraph x y m) hle hG
  let M₀ := unitModel (chainGraph x y m) hH
  have h2 : regCoeff M₀.cov (insert x Z) y x = 2 :=
    chain_regCoeff M₀ rfl (fun _ _ => rfl) (fun _ _ h => h) (ne_of_adj_of_isAcyclic hG hxy)
      (ne_of_adj_of_isAcyclic hG hxm) (ne_of_adj_of_isAcyclic hG hmy) hxZ hyZ hmZ
  refine ⟨onGraph M₀ G hG hle, rfl, rfl, fun S =>
    isUnit_submatrix_of_posDef (M₀.cov_posDef PosDef.one) S, ?_⟩
  change regCoeff M₀.cov (insert x Z) y x ≠ M₀.B y x
  rw [h2]
  simp [M₀, unitModel, chainGraph]

/-! #### A collider `x → c ← w` opened by `c ∈ Z`, followed by `w → y` -/

/-- The collider pattern: edges `x → c`, `w → c`, `w → y`, `x → y`. -/
def colliderGraph (x y c w : V) : Digraph V where
  Adj p q := (p = x ∧ q = c) ∨ (p = w ∧ q = c) ∨ (p = w ∧ q = y) ∨ (p = x ∧ q = y)

instance (x y c w : V) : DecidableRel (colliderGraph x y c w).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- In a model whose only edges are `x → c`, `w → c`, `w → y`, `x → y`, all with coefficient `1`,
and whose errors are uncorrelated with variance `1`, the coefficient of `x` in the regression of
`y` on `x` and a set `Z` containing `c` but not `x`, `y`, `w` is `1 / 2`. -/
theorem collider_regCoeff (M : LinearSEM V) (hΩ : M.Ω = 1) {x y c w : V}
    (hB : ∀ v u, M.B v u = if (u = x ∧ v = c) ∨ (u = w ∧ v = c) ∨ (u = w ∧ v = y) ∨
      (u = x ∧ v = y) then 1 else 0)
    (hE : ∀ p q, M.G.Adj p q →
      (p = x ∧ q = c) ∨ (p = w ∧ q = c) ∨ (p = w ∧ q = y) ∨ (p = x ∧ q = y))
    (nxy : x ≠ y) (nxc : x ≠ c) (nwc : w ≠ c) (nwy : w ≠ y) (ncy : c ≠ y) (nwx : w ≠ x)
    {Z : Finset V} (hxZ : x ∉ Z) (hyZ : y ∉ Z) (hwZ : w ∉ Z) (hcZ : c ∈ Z) :
    regCoeff M.cov (insert x Z) y x = 1 / 2 := by
  have anc_x : ∀ a, ReflTransGen M.G.Adj a x → a = x := fun a h =>
    mem_of_reflTransGen (S := {x}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h rfl
  have anc_w : ∀ a, ReflTransGen M.G.Adj a w → a = w := fun a h =>
    mem_of_reflTransGen (S := {w}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h rfl
  have anc_c : ∀ a, ReflTransGen M.G.Adj a c → a = c ∨ a = x ∨ a = w := fun a h =>
    mem_of_reflTransGen (S := {c, x, w}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h (by simp)
  have anc_y : ∀ a, ReflTransGen M.G.Adj a y → a = y ∨ a = w ∨ a = x := fun a h =>
    mem_of_reflTransGen (S := {y, w, x}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h (by simp)
  have anc_s : ∀ s, s ≠ c → s ≠ y → ∀ a, ReflTransGen M.G.Adj a s → a = s :=
    fun s hsc hsy a h => mem_of_reflTransGen (S := {s}) (fun p q hpq hq => by
      rcases hE p q hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all) h rfl
  have hBc : ∀ k, M.B c k = if k = x ∨ k = w then 1 else 0 := fun k => by
    rw [hB]; by_cases hk : k = x <;> by_cases hk' : k = w <;> simp [hk, hk', ncy]
  have hBy : ∀ k, M.B y k = if k = w ∨ k = x then 1 else 0 := fun k => by
    rw [hB]; by_cases hk : k = x <;> by_cases hk' : k = w <;> simp [hk, hk', Ne.symm ncy]
  have sum_c : ∀ u, ∑ k, M.B c k * M.T k u = M.T x u + M.T w u := fun u => by
    rw [sum_eq_sum_of_support {x, w} fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [hBc, hk.1, hk.2], Finset.sum_pair (Ne.symm nwx)]
    simp [hBc]
  have sum_y : ∀ u, ∑ k, M.B y k * M.T k u = M.T w u + M.T x u := fun u => by
    rw [sum_eq_sum_of_support {w, x} fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [hBy, hk.1, hk.2], Finset.sum_pair nwx]
    simp [hBy]
  have Twx : M.T w x = 0 := M.T_apply_eq_zero fun h => Ne.symm nwx (anc_w x h)
  have Txw : M.T x w = 0 := M.T_apply_eq_zero fun h => nwx (anc_x w h)
  have Tcx : M.T c x = 1 := by
    rw [T_apply_rec, sum_c, Twx, M.T_apply_self]; norm_num [Ne.symm nxc]
  have Tcw : M.T c w = 1 := by
    rw [T_apply_rec, sum_c, Txw, M.T_apply_self]; norm_num [Ne.symm nwc]
  have Tyx : M.T y x = 1 := by
    rw [T_apply_rec, sum_y, Twx, M.T_apply_self]; norm_num [Ne.symm nxy]
  have Tyw : M.T y w = 1 := by
    rw [T_apply_rec, sum_y, Txw, M.T_apply_self]; norm_num [Ne.symm nwy]
  have Tyc : M.T y c = 0 := M.T_apply_eq_zero fun h =>
    (anc_y c h).elim ncy fun h' => h'.elim (Ne.symm nwc) (Ne.symm nxc)
  have Tx0 : ∀ a, a ≠ x → M.T x a = 0 := fun a h1 =>
    M.T_apply_eq_zero fun h => h1 (anc_x a h)
  have Tc0 : ∀ a, a ≠ c → a ≠ x → a ≠ w → M.T c a = 0 := fun a h1 h2 h3 =>
    M.T_apply_eq_zero fun h => (anc_c a h).elim h1 fun h' => h'.elim h2 h3
  have sum_cxw : ∀ f : V → ℝ, (∀ a, a ≠ c → a ≠ x → a ≠ w → f a = 0) →
      ∑ a, f a = f c + (f x + f w) := fun f hf => by
    rw [sum_eq_sum_of_support {c, x, w} fun a ha => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      exact hf a ha.1 ha.2.1 ha.2.2, Finset.sum_insert (by simp [Ne.symm nxc, Ne.symm nwc]),
      Finset.sum_pair (Ne.symm nwx)]
  have Cxx : M.cov x x = 1 := by
    rw [cov_apply_of_eq_one M hΩ, sum_eq_sum_of_support {x} fun a ha => by
      simp [Tx0 a (by simpa using ha)], Finset.sum_singleton, M.T_apply_self]
    norm_num
  have Cxc : M.cov x c = 1 := by
    rw [cov_apply_of_eq_one M hΩ, sum_eq_sum_of_support {x} fun a ha => by
      simp [Tx0 a (by simpa using ha)], Finset.sum_singleton, M.T_apply_self, Tcx]
    norm_num
  have Cxy : M.cov x y = 1 := by
    rw [cov_apply_of_eq_one M hΩ, sum_eq_sum_of_support {x} fun a ha => by
      simp [Tx0 a (by simpa using ha)], Finset.sum_singleton, M.T_apply_self, Tyx]
    norm_num
  have Ccc : M.cov c c = 3 := by
    rw [cov_apply_of_eq_one M hΩ, sum_cxw _ fun a h1 h2 h3 => by simp [Tc0 a h1 h2 h3],
      M.T_apply_self, Tcx, Tcw]
    norm_num
  have Ccy : M.cov c y = 2 := by
    rw [cov_apply_of_eq_one M hΩ, sum_cxw _ fun a h1 h2 h3 => by simp [Tc0 a h1 h2 h3],
      M.T_apply_self, Tcx, Tcw, Tyc, Tyx, Tyw]
    norm_num
  have Cs : ∀ s, s ≠ x → s ≠ y → s ≠ w → s ≠ c → ∀ t, (t = x ∨ t = c ∨ t = y) →
      M.cov s t = 0 := by
    intro s hsx hsy hsw hsc t ht
    rw [cov_apply_of_eq_one M hΩ, sum_eq_sum_of_support {s} fun a ha => by
      have : M.T s a = 0 := M.T_apply_eq_zero fun h =>
        (by simpa using ha : a ≠ s) (anc_s s hsc hsy a h)
      simp [this], Finset.sum_singleton, M.T_apply_self, one_mul]
    refine M.T_apply_eq_zero fun h => ?_
    rcases ht with rfl | rfl | rfl
    · exact hsx (anc_x s h)
    · exact (anc_c s h).elim hsc fun h' => h'.elim hsx hsw
    · exact (anc_y s h).elim hsy fun h' => h'.elim hsw hsx
  set β : V → ℝ := fun v => if v = x then 1 / 2 else if v = c then 1 / 2 else 0 with hβdef
  have hpair : IsRegCoeff M.cov {x, c} y β := by
    refine (isRegCoeff_pair_iff nxc (M.cov_symm c x) (by rw [Cxx, Ccc, Cxc]; norm_num)).2
      ⟨fun v hv => ?_, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      simp [hβdef, hv.1, hv.2]
    · rw [Ccc, Cxy, Cxc, Ccy, Cxx]; simp [hβdef]; norm_num
    · rw [Ccc, Cxy, Cxc, Ccy, Cxx]; simp [hβdef, Ne.symm nxc]; norm_num
  have hβ : IsRegCoeff M.cov (insert x Z) y β := by
    refine isRegCoeff_of_uncorrelated hpair (Finset.insert_subset_insert _
      (Finset.singleton_subset_iff.2 hcZ)) fun s hs hs₁ => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs₁
    have hsZ : s ∈ Z := (Finset.mem_insert.1 hs).resolve_left hs₁.1
    have hsy : s ≠ y := fun h => hyZ (h ▸ hsZ)
    have hsw : s ≠ w := fun h => hwZ (h ▸ hsZ)
    refine ⟨Cs s hs₁.1 hsy hsw hs₁.2 y (Or.inr (Or.inr rfl)), fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact Cs s hs₁.1 hsy hsw hs₁.2 t (Or.inl rfl)
    · rw [Finset.mem_singleton.1 ht]; exact Cs s hs₁.1 hsy hsw hs₁.2 c (Or.inr (Or.inl rfl))
  have hu : IsUnit (subCov M.cov (insert x Z)) :=
    isUnit_submatrix_of_posDef (M.cov_posDef (hΩ ▸ PosDef.one)) _
  rw [(regCoeff_isRegCoeff y hu).unique hu hβ]
  simp [hβdef]

/-- **A collider opened by the conditioning set, on an arbitrary graph.** Let `G` be acyclic with
edges `x → y`, `x → c`, `w → c` and `w → y`, with `w ≠ x`, and let `Z` contain `c` but neither
`x` nor `w` nor any descendant of `y`. Then `x → c ← w → y` is an open path of `G` with `x → y`
deleted (the collider `c` is in `Z`), and there is a linear SEM on `G` with uncorrelated
unit-variance errors at which the coefficient of `x` in the regression of `y` on `x` and `Z`
differs from the path coefficient. -/
theorem exists_ne_of_collider {G : Digraph V} (hG : G.IsAcyclic) {x y c w : V} {Z : Finset V}
    (hxy : G.Adj x y) (hxc : G.Adj x c) (hwc : G.Adj w c) (hwy : G.Adj w y) (hwx : w ≠ x)
    (hxZ : x ∉ Z) (hwZ : w ∉ Z) (hcZ : c ∈ Z) (hZ : ∀ s ∈ Z, ¬ ReflTransGen G.Adj y s) :
    ∃ M : LinearSEM V, M.G = G ∧ M.Ω = 1 ∧ (∀ S : Finset V, IsUnit (subCov M.cov S)) ∧
      regCoeff M.cov (insert x Z) y x ≠ M.B y x := by
  have hyZ : y ∉ Z := fun h => hZ y h ReflTransGen.refl
  have hle : ∀ p q, (colliderGraph x y c w).Adj p q → G.Adj p q := by
    intro p q h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> assumption
  have hH : (colliderGraph x y c w).IsAcyclic :=
    Digraph.IsAcyclic.anti (H := colliderGraph x y c w) hle hG
  let M₀ := unitModel (colliderGraph x y c w) hH
  have h12 : regCoeff M₀.cov (insert x Z) y x = 1 / 2 :=
    collider_regCoeff M₀ rfl (fun _ _ => rfl) (fun _ _ h => h) (ne_of_adj_of_isAcyclic hG hxy)
      (ne_of_adj_of_isAcyclic hG hxc) (ne_of_adj_of_isAcyclic hG hwc)
      (ne_of_adj_of_isAcyclic hG hwy) (fun h => hyZ (h ▸ hcZ)) hwx hxZ hyZ hwZ hcZ
  refine ⟨onGraph M₀ G hG hle, rfl, rfl, fun S =>
    isUnit_submatrix_of_posDef (M₀.cov_posDef PosDef.one) S, ?_⟩
  change regCoeff M₀.cov (insert x Z) y x ≠ M₀.B y x
  rw [h12]
  norm_num [M₀, unitModel, colliderGraph]

end General

end SingleDoorConverse

end LinearSEM

end CausalInference
