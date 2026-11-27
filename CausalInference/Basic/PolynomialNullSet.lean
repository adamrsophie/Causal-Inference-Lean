/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Zero sets of nonzero polynomials are Lebesgue null

The zero set `{x : Fin n → ℝ | eval x p = 0}` of a nonzero multivariate polynomial
`p : MvPolynomial (Fin n) ℝ` has Lebesgue measure zero (`volume_zeroSet_eq_zero`).

The proof is by induction on `n`. For `n = 0` a nonzero polynomial is a nonzero constant. For
`n + 1`, write `p` as a polynomial in the first variable with coefficients in
`MvPolynomial (Fin n) ℝ` (`MvPolynomial.finSuccEquiv`) and let `c ≠ 0` be its leading
coefficient. At a point `s` of the remaining variables with `c(s) ≠ 0`, the specialized
polynomial in the first variable is nonzero and has finitely many roots, so the slice of the
zero set over `s` is null; the points `s` with `c(s) = 0` form a null set by induction. Fubini
(`MeasureTheory.Measure.prod_apply_symm`) concludes.

This is the step that turns "the bias is a nonzero polynomial in the parameters" into
"the bias vanishes only on a set of measure zero" in measure-zero statements such as the
converse of the single-door criterion (Pearl 2009, Theorem 5.3.1).
-/

@[expose] public section

namespace CausalInference

open MeasureTheory MvPolynomial

/-- The inverse of `MeasurableEquiv.piFinSuccAbove` at `0` is `Fin.cons`. -/
theorem piFinSuccAbove_zero_symm_apply {n : ℕ} (y : ℝ) (s : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (y, s) =
      Fin.cons y s := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

/-- **The zero set of a nonzero real polynomial in `n` variables is Lebesgue null.** -/
theorem volume_zeroSet_eq_zero : ∀ {n : ℕ} {p : MvPolynomial (Fin n) ℝ}, p ≠ 0 →
    volume {x : Fin n → ℝ | eval x p = 0} = 0
  | 0, p, hp => by
    have : {x : Fin 0 → ℝ | eval x p = 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hp (MvPolynomial.funext fun y => by rw [Subsingleton.elim y x, hx, map_zero])
    rw [this, measure_empty]
  | n + 1, p, hp => by
    set q := finSuccEquiv ℝ n p
    have hq : q ≠ 0 := fun h => hp ((finSuccEquiv ℝ n).injective (h.trans (map_zero _).symm))
    have hc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hq
    have hN := volume_zeroSet_eq_zero hc
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hmp : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      measurePreserving_piFinSuccAbove (fun _ => volume) 0
    set S := {x : Fin (n + 1) → ℝ | eval x p = 0}
    have hS : MeasurableSet S := (isClosed_eq (continuous_eval p) continuous_const).measurableSet
    have hae : ∀ᵐ s ∂(volume : Measure (Fin n → ℝ)),
        (volume : Measure ℝ) ((fun y => (y, s)) ⁻¹' (e.symm ⁻¹' S)) = 0 := by
      refine ae_iff.2 (measure_mono_null ?_ hN)
      intro s hs
      simp only [Set.mem_ofPred_eq] at hs ⊢
      by_contra hcs
      apply hs
      have hpoly : Polynomial.map (eval s) q ≠ 0 := by
        intro h0
        have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (eval s) hcs
        rw [h0, Polynomial.leadingCoeff_zero] at this
        exact hcs this.symm
      refine Set.Finite.measure_zero ((Polynomial.finite_setOfPred_isRoot hpoly).subset
        fun y hy => ?_) _
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, S] at hy
      rw [show e.symm (y, s) = Fin.cons y s from piFinSuccAbove_zero_symm_apply y s,
        eval_eq_eval_mv_eval'] at hy
      exact hy
    refine (hmp.symm.measure_preimage hS.nullMeasurableSet).symm.trans ?_
    rw [Measure.prod_apply_symm (e.symm.measurable hS), lintegral_congr_ae hae, lintegral_zero]

end CausalInference
