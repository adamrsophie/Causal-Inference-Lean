/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.GaussMarkov
public import CausalInference.MetaAnalysis.CommonEffect
public import CausalInference.IndirectComparison.CommonComparator

/-!
# Network meta-analysis: pooling direct and indirect evidence in a triangle

The triangle network has treatments `a = 0`, `b = 1`, `c = 2` and one comparison of each pair:
comparison `0` is `a → b`, comparison `1` is `a → c`, comparison `2` is `b → c`
(`triangleTail`, `triangleHead`). With reference `a` and basic parameters `(d_ab, d_ac)` the
reduced design is `triangleDesign` (`triangleDesign_mulVec`), and the network is connected
(`comparisonGraph_triangle_connected`).

For independent comparison estimates `y_ab, y_ac, y_bc` with variances `v_ab, v_ac, v_bc > 0`,
the generalized least squares estimate of `d_ab` is the inverse variance pooling of the direct
estimate `y_ab` (variance `v_ab`) and the indirect estimate `y_ac - y_bc` (the
`indirectEstimate` of Bucher et al. 1997, variance `v_ac + v_bc`), and likewise for `d_ac`
(`triangle_glsEstimate`). In the linear model of the triangle the network estimate of `d_ab` is
unbiased with variance `1 / (1 / v_ab + 1 / (v_ac + v_bc))`, strictly smaller than the variance
of the direct and of the indirect estimate, and no linear unbiased estimator of `d_ab` has a
smaller variance (`triangle_pooling`).

The identification of a network estimate with a solution of the normal equations
(`glsEstimate_eq_of_normal`) is the general step: a vector solving `(Xᵀ V⁻¹ X) β = Xᵀ V⁻¹ y` is
the generalized least squares estimate when `Xᵀ V⁻¹ X` is invertible.

## Main definitions

* `triangleTail`, `triangleHead`, `triangleDesign`.

## Main results

* `glsEstimate_eq_of_normal`, `inv_diagonal_eq`, `ivwEstimate_two_pooling`.
* `triangleDesign_mulVec`, `comparisonGraph_triangle_connected`,
  `triangleDesign_injective`.
* `triangle_gram_mulVec`, `triangle_rhs`, `ivwEstimate_two`, `triangle_glsEstimate`,
  `triangle_pooling`.

## References

* H. C. Bucher, G. H. Guyatt, L. E. Griffith and S. D. Walter, *The results of direct and
  indirect treatment comparisons in meta-analysis of randomized controlled trials*, Journal of
  Clinical Epidemiology 50 (1997).
* G. Lu and A. E. Ades, *Combination of direct and indirect evidence in mixed treatment
  comparisons*, Statistics in Medicine 23 (2004).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix MeasureTheory ProbabilityTheory BiasAnalysis.MeasurementError MetaAnalysis
  IndirectComparison

/-! ### The normal equations -/

section Normal

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

/-- **A solution of the normal equations is the generalized least squares estimate**: if
`Xᵀ V⁻¹ X` is invertible and `(Xᵀ V⁻¹ X) β = Xᵀ V⁻¹ y`, then `β = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y`. -/
theorem glsEstimate_eq_of_normal {X : Matrix n p ℝ} {V : Matrix n n ℝ}
    (hM : IsUnit (Xᵀ * V⁻¹ * X)) {y : n → ℝ} {β : p → ℝ}
    (hβ : (Xᵀ * V⁻¹ * X) *ᵥ β = Xᵀ *ᵥ (V⁻¹ *ᵥ y)) : glsEstimate X V y = β := by
  rw [glsEstimate, glsMatrix, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, ← hβ,
    mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hM), one_mulVec]

/-- The inverse of a diagonal matrix with nonzero entries. -/
theorem inv_diagonal_eq {v : n → ℝ} (hv : ∀ i, v i ≠ 0) :
    (diagonal v)⁻¹ = diagonal fun i => (v i)⁻¹ := by
  refine inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (hv i)

end Normal

/-! ### Pooling two unbiased estimates -/

/-- **Pooling a direct and an indirect estimate** (Bucher et al. 1997; Lu and Ades 2004). Let
`X_d` and `X_i` be uncorrelated, square integrable estimates of the same effect `d` at every
`d`, with variances `v_d, v_i > 0`. Then their inverse variance pooling is unbiased with
variance `1 / (1 / v_d + 1 / v_i)`, and every linear combination `a₁ X_d + a₂ X_i` that is
unbiased at every `d` has at least this variance. -/
theorem ivwEstimate_two_pooling {Ω : Type*} [MeasurableSpace Ω] {P : ℝ → Measure Ω}
    [∀ d, IsProbabilityMeasure (P d)] {Xd Xi : Ω → ℝ} {vd vi : ℝ} (hvd : 0 < vd) (hvi : 0 < vi)
    (hXd : ∀ d, MemLp Xd 2 (P d)) (hXi : ∀ d, MemLp Xi 2 (P d))
    (hunc : ∀ d, cov[Xd, Xi; P d] = 0) (hEd : ∀ d, ∫ ω, Xd ω ∂P d = d)
    (hEi : ∀ d, ∫ ω, Xi ω ∂P d = d) (hVd : ∀ d, Var[Xd; P d] = vd)
    (hVi : ∀ d, Var[Xi; P d] = vi) (d : ℝ) :
    ∫ ω, ivwEstimate ![vd, vi] ![Xd ω, Xi ω] ∂P d = d ∧
      Var[fun ω => ivwEstimate ![vd, vi] ![Xd ω, Xi ω]; P d] = 1 / (1 / vd + 1 / vi) ∧
      ∀ a₁ a₂ : ℝ, (∀ d', ∫ ω, a₁ * Xd ω + a₂ * Xi ω ∂P d' = d') →
        1 / (1 / vd + 1 / vi) ≤ Var[fun ω => a₁ * Xd ω + a₂ * Xi ω; P d] := by
  set Z : Fin 2 → Ω → ℝ := ![Xd, Xi]
  have hz : ∀ ω, (fun i => Z i ω) = ![Xd ω, Xi ω] := fun ω => by
    funext i; fin_cases i <;> rfl
  have hv : ∀ i, 0 < (![vd, vi] : Fin 2 → ℝ) i := by
    intro i; fin_cases i
    · exact hvd
    · exact hvi
  have hmem : ∀ d i, MemLp (Z i) 2 (P d) := by
    intro d i; fin_cases i
    · exact hXd d
    · exact hXi d
  have hvar : ∀ d i, Var[Z i; P d] = (![vd, vi] : Fin 2 → ℝ) i := by
    intro d i; fin_cases i
    · exact hVd d
    · exact hVi d
  have hZunc : ∀ d i j, i ≠ j → cov[Z i, Z j; P d] = 0 := by
    intro d i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hunc d
    · rw [covariance_comm]; exact hunc d
    · exact absurd rfl hij
  have hsum : ∑ i, ivWeight (![vd, vi] : Fin 2 → ℝ) i = 1 / vd + 1 / vi := by
    simp [ivWeight, Fin.sum_univ_two]
  have hlin : ∀ d' a₁ a₂, ∫ ω, a₁ * Xd ω + a₂ * Xi ω ∂P d' = a₁ * d' + a₂ * d' := by
    intro d' a₁ a₂
    rw [integral_add (((hXd d').integrable one_le_two).const_mul _)
      (((hXi d').integrable one_le_two).const_mul _), integral_const_mul, integral_const_mul,
      hEd, hEi]
  refine ⟨?_, ?_, fun a₁ a₂ ha => ?_⟩
  · simp_rw [← hz]
    refine integral_ivwEstimate hv (fun i => (hmem d i).integrable one_le_two) fun i => ?_
    fin_cases i
    · exact hEd d
    · exact hEi d
  · simp_rw [← hz]
    rw [variance_ivwEstimate hv (hmem d) (hvar d) (hZunc d), hsum]
  · have h1 : a₁ + a₂ = 1 := by
      have := ha 1
      rw [hlin] at this
      linarith
    have hge := variance_sum_mul_ge hv (hmem d) (hvar d) (hZunc d) (c := ![a₁, a₂])
      (by simpa [Fin.sum_univ_two] using h1)
    rw [hsum] at hge
    convert hge using 2
    funext ω
    simp [Z, Fin.sum_univ_two]

/-! ### The triangle network -/

/-- The tails of the triangle comparisons `a → b`, `a → c`, `b → c`. -/
def triangleTail : Fin 3 → Fin 3 := ![0, 0, 1]

/-- The heads of the triangle comparisons `a → b`, `a → c`, `b → c`. -/
def triangleHead : Fin 3 → Fin 3 := ![1, 2, 2]

/-- The **design of the triangle** in the basic parameters `(d_ab, d_ac)`: the comparison
`a → b` has mean `d_ab`, `a → c` has mean `d_ac`, and `b → c` has mean `d_ac - d_ab`. -/
def triangleDesign : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; -1, 1]

/-- The triangle design gives the contrasts of the level vector `(0, d_ab, d_ac)`. -/
theorem triangleDesign_mulVec (β : Fin 2 → ℝ) :
    triangleDesign *ᵥ β = incidenceMatrix triangleTail triangleHead *ᵥ ![0, β 0, β 1] := by
  funext e
  rw [incidenceMatrix_mulVec]
  fin_cases e <;> simp [triangleDesign, triangleTail, triangleHead, mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- The triangle network is connected. -/
theorem comparisonGraph_triangle_connected :
    (comparisonGraph triangleTail triangleHead).Connected := by
  have h01 : (comparisonGraph triangleTail triangleHead).Adj 0 1 :=
    comparisonGraph_adj_of_ne (tail := triangleTail) (head := triangleHead) 0 (by decide)
  have h02 : (comparisonGraph triangleTail triangleHead).Adj 0 2 :=
    comparisonGraph_adj_of_ne (tail := triangleTail) (head := triangleHead) 1 (by decide)
  have hr : ∀ k, (comparisonGraph triangleTail triangleHead).Reachable 0 k := by
    intro k
    fin_cases k
    · exact SimpleGraph.Reachable.refl _
    · exact h01.reachable
    · exact h02.reachable
  exact ⟨fun a b => (hr a).symm.trans (hr b)⟩

/-- The triangle design has full column rank. -/
theorem triangleDesign_injective : Function.Injective triangleDesign.mulVec := by
  intro β β' h
  have h0 : β 0 = β' 0 := by
    simpa [triangleDesign, mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 0
  have h1 : β 1 = β' 1 := by
    simpa [triangleDesign, mulVec, dotProduct, Fin.sum_univ_two] using congrFun h 1
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- The Gram matrix of the triangle with weights `1 / v`, applied to a parameter. -/
theorem triangle_gram_mulVec {v : Fin 3 → ℝ} (hv : ∀ i, v i ≠ 0) (β : Fin 2 → ℝ) :
    (triangleDesignᵀ * (diagonal v)⁻¹ * triangleDesign) *ᵥ β =
      ![(1 / v 0 + 1 / v 2) * β 0 - 1 / v 2 * β 1,
        -(1 / v 2) * β 0 + (1 / v 1 + 1 / v 2) * β 1] := by
  rw [inv_diagonal_eq hv]
  funext k
  fin_cases k <;> simp [triangleDesign, mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three,
    Matrix.mul_apply, diagonal_apply]
  ring

/-- The right side `Xᵀ V⁻¹ y` of the normal equations of the triangle. -/
theorem triangle_rhs {v : Fin 3 → ℝ} (hv : ∀ i, v i ≠ 0) (y : Fin 3 → ℝ) :
    triangleDesignᵀ *ᵥ ((diagonal v)⁻¹ *ᵥ y) = ![y 0 / v 0 - y 2 / v 2, y 1 / v 1 + y 2 / v 2] := by
  rw [inv_diagonal_eq hv]
  funext k
  fin_cases k <;> simp [triangleDesign, mulVec, dotProduct, Fin.sum_univ_three, div_eq_inv_mul]
  ring

/-- Inverse variance pooling of two estimates in closed form. -/
theorem ivwEstimate_two {a b x z : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ivwEstimate ![a, b] ![x, z] = (x * b + z * a) / (a + b) := by
  rw [ivwEstimate_eq_sum]
  simp only [ivWeight, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp
  ring

/-- **Network estimates in the triangle are pooled direct and indirect estimates.** With
independent comparison estimates of variances `v_ab, v_ac, v_bc > 0` (covariance `diag(v)`),
the generalized least squares estimate of `d_ab` is the inverse variance pooling of the direct
estimate `y_ab` (variance `v_ab`) and the indirect estimate `y_ac - y_bc` (variance
`v_ac + v_bc`), and the estimate of `d_ac` pools `y_ac` with `y_ab + y_bc`. -/
theorem triangle_glsEstimate {v : Fin 3 → ℝ} (hv : ∀ i, 0 < v i) (y : Fin 3 → ℝ) :
    glsEstimate triangleDesign (diagonal v) y 0 =
        ivwEstimate ![v 0, v 1 + v 2] ![y 0, y 1 - y 2] ∧
      glsEstimate triangleDesign (diagonal v) y 1 =
        ivwEstimate ![v 1, v 0 + v 2] ![y 1, y 0 + y 2] := by
  have hV : (diagonal v).PosDef := posDef_diagonal_iff.2 hv
  have hM := isUnit_gram_inv hV triangleDesign_injective
  have hv0 := hv 0
  have hv1 := hv 1
  have hv2 := hv 2
  have hne : ∀ i, v i ≠ 0 := fun i => (hv i).ne'
  have hS : v 0 + v 1 + v 2 ≠ 0 := by positivity
  rw [ivwEstimate_two hv0 (by positivity), ivwEstimate_two hv1 (by positivity)]
  have hsol := glsEstimate_eq_of_normal hM (y := y)
    (β := ![(y 0 * (v 1 + v 2) + (y 1 - y 2) * v 0) / (v 0 + (v 1 + v 2)),
      (y 1 * (v 0 + v 2) + (y 0 + y 2) * v 1) / (v 1 + (v 0 + v 2))]) (by
    rw [triangle_gram_mulVec hne, triangle_rhs hne]
    have e1 : v 0 + (v 1 + v 2) = v 0 + v 1 + v 2 := by ring
    have e2 : v 1 + (v 0 + v 2) = v 0 + v 1 + v 2 := by ring
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, e1, e2]
    congr 1
    · field_simp
      ring
    · congr 1
      field_simp
      ring)
  rw [hsol]
  exact ⟨rfl, rfl⟩

/-- **Pooling direct and indirect evidence in the triangle network** (Bucher et al. 1997; Lu and
Ades 2004). In the linear model of the triangle with covariance `diag(v)`, `v > 0`:

* the network estimate of `d_ab` is the inverse variance pooling of the direct estimate `y_ab`
  and the indirect estimate `y_ac - y_bc` (`indirectEstimate`);
* it is unbiased, with variance `1 / (1 / v_ab + 1 / (v_ac + v_bc))`;
* this variance is strictly smaller than the variance `v_ab` of the direct estimate and the
  variance `v_ac + v_bc` of the indirect estimate;
* every linear estimator `wᵀ y` unbiased for `d_ab` at every parameter has at least this
  variance. -/
theorem triangle_pooling {Ω : Type*} [MeasurableSpace Ω] {P : (Fin 2 → ℝ) → Measure Ω}
    {Y : Fin 3 → Ω → ℝ} {v : Fin 3 → ℝ} (hv : ∀ i, 0 < v i)
    (h : IsLinearModel (Fin 3) P Y triangleDesign (diagonal v)) (β : Fin 2 → ℝ) :
    (∀ ω, glsEstimate triangleDesign (diagonal v) (fun e => Y e ω) 0 =
      ivwEstimate ![v 0, v 1 + v 2] ![Y 0 ω, indirectEstimate (Y 1) (Y 2) ω]) ∧
      ∫ ω, glsEstimate triangleDesign (diagonal v) (fun e => Y e ω) 0 ∂P β = β 0 ∧
      Var[fun ω => glsEstimate triangleDesign (diagonal v) (fun e => Y e ω) 0; P β] =
        1 / (1 / v 0 + 1 / (v 1 + v 2)) ∧
      1 / (1 / v 0 + 1 / (v 1 + v 2)) < v 0 ∧ 1 / (1 / v 0 + 1 / (v 1 + v 2)) < v 1 + v 2 ∧
      ∀ w : Fin 3 → ℝ, (∀ β', ∫ ω, w ⬝ᵥ (fun e => Y e ω) ∂P β' = β' 0) →
        1 / (1 / v 0 + 1 / (v 1 + v 2)) ≤ Var[fun ω => w ⬝ᵥ (fun e => Y e ω); P β] := by
  have hV : (diagonal v).PosDef := posDef_diagonal_iff.2 hv
  have := h.isProbabilityMeasure β
  have hpt : ∀ ω, glsEstimate triangleDesign (diagonal v) (fun e => Y e ω) 0 =
      ivwEstimate ![v 0, v 1 + v 2] ![Y 0 ω, indirectEstimate (Y 1) (Y 2) ω] :=
    fun ω => (triangle_glsEstimate hv _).1
  have hmem := h.memLp β
  have hcov : ∀ i j, cov[Y i, Y j; P β] = diagonal v i j := fun i j => by
    rw [← h.covMatrix_eq β]; rfl
  have hvar : ∀ i, Var[Y i; P β] = v i := fun i => by
    rw [← covariance_self (hmem i).aestronglyMeasurable.aemeasurable, hcov, diagonal_apply_eq]
  have hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P β] = 0 := fun i j hij => by
    rw [hcov, diagonal_apply_ne _ hij]
  set Z : Fin 2 → Ω → ℝ := ![Y 0, indirectEstimate (Y 1) (Y 2)]
  have hZmem : ∀ i, MemLp (Z i) 2 (P β) := by
    intro i; fin_cases i
    · exact hmem 0
    · exact (hmem 1).sub (hmem 2)
  have hZvar : ∀ i, Var[Z i; P β] = ![v 0, v 1 + v 2] i := by
    intro i; fin_cases i
    · exact hvar 0
    · change Var[indirectEstimate (Y 1) (Y 2); P β] = v 1 + v 2
      rw [variance_indirectEstimate (hmem 1) (hmem 2) (hunc 1 2 (by decide)), hvar, hvar]
  have hZunc : ∀ i j, i ≠ j → cov[Z i, Z j; P β] = 0 := by
    have h01 : cov[Y 0, indirectEstimate (Y 1) (Y 2); P β] = 0 := by
      rw [show indirectEstimate (Y 1) (Y 2) = fun ω => Y 1 ω - Y 2 ω from rfl,
        covariance_fun_sub_right (hmem 0) (hmem 1) (hmem 2), hunc 0 1 (by decide),
        hunc 0 2 (by decide), sub_zero]
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01
    · rw [covariance_comm]; exact h01
    · exact absurd rfl hij
  have hv' : ∀ i, 0 < (![v 0, v 1 + v 2] : Fin 2 → ℝ) i := by
    intro i; fin_cases i
    · exact hv 0
    · exact add_pos (hv 1) (hv 2)
  have hfun : (fun ω => glsEstimate triangleDesign (diagonal v) (fun e => Y e ω) 0) =
      fun ω => ivwEstimate ![v 0, v 1 + v 2] (fun i => Z i ω) := by
    funext ω
    rw [hpt]
    congr 1
    funext i; fin_cases i <;> rfl
  have hsum : ∑ i, ivWeight (![v 0, v 1 + v 2] : Fin 2 → ℝ) i = 1 / v 0 + 1 / (v 1 + v 2) := by
    simp [ivWeight, Fin.sum_univ_two]
  have hVar : Var[fun ω => glsEstimate triangleDesign (diagonal v) (fun e => Y e ω) 0; P β] =
      1 / (1 / v 0 + 1 / (v 1 + v 2)) := by
    rw [hfun, variance_ivwEstimate hv' hZmem hZvar hZunc, hsum]
  have hp0 := hv 0
  have hp12 := add_pos (hv 1) (hv 2)
  refine ⟨hpt, h.integral_glsEstimate hV triangleDesign_injective β 0, hVar, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    have : 0 < v 0 * (1 / (v 1 + v 2)) := by positivity
    rw [mul_add, mul_one_div_cancel hp0.ne']
    linarith
  · rw [div_lt_iff₀ (by positivity)]
    have : 0 < (v 1 + v 2) * (1 / v 0) := by positivity
    rw [mul_add, mul_one_div_cancel hp12.ne']
    linarith
  · intro w hw
    have hge := (h.variance_dotProduct_ge hV triangleDesign_injective (Pi.single 0 1)
      (a := w) (fun β' => by rw [hw, single_dotProduct, one_mul]) β)
    rw [← hge.2.1] at hge
    have e1 : Var[fun ω => (Pi.single 0 1 : Fin 2 → ℝ) ⬝ᵥ
        glsEstimate triangleDesign (diagonal v) (fun e => Y e ω); P β] =
        Var[fun ω => glsEstimate triangleDesign (diagonal v) (fun e => Y e ω) 0; P β] := by
      congr 1; funext ω; rw [single_dotProduct, one_mul]
    rw [e1, hVar] at hge
    exact hge.2.2.1

end NetworkMetaAnalysis

end CausalInference
