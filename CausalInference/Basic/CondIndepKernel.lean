/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Basic.CondIndepIntersection
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional independence and conditional distributions

For random variables `U` and `V` with standard Borel value spaces and any conditioning variable
`W`, `U ⫫ V | W` (Mathlib's `ProbabilityTheory.CondIndepFun` given the σ-algebra of `W`) holds
if and only if the conditional distribution of the pair `(U, V)` given `W` is, for almost every
value of `W`, the product of the conditional distributions of `U` and of `V` given `W`.

A conditional distribution is determined only almost everywhere under the law of the
conditioning variable. A statement about it at every value therefore depends on the version
chosen: the file gives a model in which `U ⫫ V | W` holds, the product kernel is a version of the
conditional law of `(U, V)` given `W` that factorizes at every value, and another version fails
to be a product measure at a value of probability zero.

## Main results

* `condIndepFun_iff_condDistrib_prod_ae_eq_prod`: the factorization of the conditional joint law.
* `exists_condDistrib_version_not_prod`: for a constant conditioning variable, a version of the
  conditional law of a pair of binary variables that is not a product measure at the null value.
* `condDistrib_version_dependence`: the concrete model with both versions.

The conditional law of `V` given `(W, U)` is that of `V` given `W` under `U ⫫ V | W`: this is
Mathlib's `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`.

## References

* J. T. Chang and D. Pollard, *Conditioning as disintegration*, Statistica Neerlandica 51
  (1997).
-/

@[expose] public section

namespace CausalInference

open MeasureTheory ProbabilityTheory
open scoped ENNReal

section Factorization

variable {Ω α β γ : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] [MeasurableSpace γ]
  {μ : Measure Ω} [IsFiniteMeasure μ] {U : Ω → α} {V : Ω → β} {W : Ω → γ}

/-- **Conditional independence is the factorization of the conditional joint law**: for `U` and
`V` with standard Borel value spaces, `U ⫫ V | W` if and only if the conditional distribution of
`(U, V)` given `W` equals, for almost every value of `W`, the product of the conditional
distributions of `U` and `V` given `W`. -/
theorem condIndepFun_iff_condDistrib_prod_ae_eq_prod (hU : Measurable U) (hV : Measurable V)
    (hW : Measurable W) :
    CondIndepFun (MeasurableSpace.comap W inferInstance) hW.comap_le U V μ ↔
      condDistrib (fun ω => (U ω, V ω)) W μ =ᵐ[μ.map W]
        condDistrib U W μ ×ₖ condDistrib V W μ := by
  rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hU hV hW,
    condDistrib_ae_eq_iff_measure_eq_compProd hW.aemeasurable (hU.prodMk hV).aemeasurable,
    Measure.compProd_eq_comp_prod]

end Factorization

/-! ### A pointwise statement depends on the version -/

section Version

/-- The diagonal law `½ (δ_(1,1) + δ_(0,0))` on `Bool × Bool` is not a product of two s-finite
measures. -/
theorem uniformBool_map_diag_ne_prod (p q : Measure Bool) [SFinite q] :
    uniformBool.map (fun b => (b, b)) ≠ p.prod q := by
  intro H
  have hD : ∀ s : Set (Bool × Bool), MeasurableSet s →
      p.prod q s = uniformBool ((fun b => (b, b)) ⁻¹' s) := fun s hs => by
    rw [← H]
    exact Measure.map_apply (by fun_prop) hs
  have h1 := hD _ ((measurableSet_singleton true).prod (measurableSet_singleton true))
  have h2 := hD _ ((measurableSet_singleton true).prod (measurableSet_singleton false))
  have h3 := hD _ ((measurableSet_singleton false).prod (measurableSet_singleton true))
  have h4 := hD _ ((measurableSet_singleton false).prod (measurableSet_singleton false))
  have e1 : (fun b : Bool => (b, b)) ⁻¹' ({true} ×ˢ {true}) = {true} := by ext b; simp
  have e2 : (fun b : Bool => (b, b)) ⁻¹' ({true} ×ˢ {false}) = ∅ := by
    ext b; cases b <;> simp
  have e3 : (fun b : Bool => (b, b)) ⁻¹' ({false} ×ˢ {true}) = ∅ := by
    ext b; cases b <;> simp
  have e4 : (fun b : Bool => (b, b)) ⁻¹' ({false} ×ˢ {false}) = {false} := by ext b; simp
  rw [Measure.prod_prod, e1, uniformBool_singleton] at h1
  rw [Measure.prod_prod, e2, measure_empty] at h2
  rw [Measure.prod_prod, e3, measure_empty] at h3
  rw [Measure.prod_prod, e4, uniformBool_singleton] at h4
  have hpt : p {true} ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at h1
    exact absurd h1.symm (by simp)
  have hqt : q {true} ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at h1
    exact absurd h1.symm (by simp)
  have hqf : q {false} = 0 := (mul_eq_zero.1 h2).resolve_left hpt
  have hpf : p {false} = 0 := (mul_eq_zero.1 h3).resolve_right hqt
  rw [hpf, zero_mul] at h4
  exact absurd h4.symm (by simp)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **A version of a conditional law that is not a product at a null value.** Let `W` be the
constant `true`, so that the value `false` has probability zero. Replacing the conditional
distribution of a pair `(U, V)` of binary variables at `false` by the diagonal law
`½ (δ_(1,1) + δ_(0,0))` gives another version of it, and that version is not a product measure
at `false`. -/
theorem exists_condDistrib_version_not_prod (U V : Ω → Bool) :
    ∃ κ : Kernel Bool (Bool × Bool), IsMarkovKernel κ ∧
      κ =ᵐ[μ.map fun _ => true] condDistrib (fun ω => (U ω, V ω)) (fun _ => true) μ ∧
      ∀ (p q : Measure Bool) [SFinite q], κ false ≠ p.prod q := by
  set D : Measure (Bool × Bool) := uniformBool.map fun b => (b, b)
  have : IsProbabilityMeasure D := by simp only [D]; infer_instance
  set κ := Kernel.piecewise (measurableSet_singleton true)
    (condDistrib (fun ω => (U ω, V ω)) (fun _ => true) μ) (Kernel.const Bool D)
  refine ⟨κ, inferInstance, ?_, fun p q _ => ?_⟩
  · rw [Measure.map_const, measure_univ, one_smul, Filter.EventuallyEq, ae_dirac_eq,
      Filter.eventually_pure]
    simp [κ, Kernel.piecewise_apply]
  · have hκ : κ false = D := by
      simp [κ, Kernel.piecewise_apply]
    rw [hκ]
    exact uniformBool_map_diag_ne_prod p q

/-- **A pointwise statement about conditional distributions depends on the version.** On
`Ω = Bool` with the uniform law, let `U` be the coin, `V` and `W` the constant `true`. Then
`U ⫫ V | W`; the product of the conditional laws of `U` and `V` given `W` is a version of the
conditional law of `(U, V)` given `W` that is a product measure at every value; and another
version of the same conditional law is not a product measure at the value `false` of `W`, which
has probability zero. That the product kernel is a product measure at every value holds by the
definition of `×ₖ`; it is stated to set it against the second version. -/
theorem condDistrib_version_dependence :
    CondIndepFun (MeasurableSpace.comap (fun _ : Bool => true) inferInstance)
        (measurable_const.comap_le) (id : Bool → Bool) (fun _ => true) uniformBool ∧
      condDistrib (fun ω : Bool => (ω, true)) (fun _ => true) uniformBool
          =ᵐ[uniformBool.map fun _ => true]
        condDistrib id (fun _ => true) uniformBool ×ₖ
          condDistrib (fun _ => true) (fun _ => true) uniformBool ∧
      (∀ z, (condDistrib id (fun _ => true) uniformBool ×ₖ
          condDistrib (fun _ => true) (fun _ => true) uniformBool) z =
        (condDistrib id (fun _ => true) uniformBool z).prod
          (condDistrib (fun _ => true) (fun _ => true) uniformBool z)) ∧
      ∃ κ : Kernel Bool (Bool × Bool), IsMarkovKernel κ ∧
        κ =ᵐ[uniformBool.map fun _ => true]
          condDistrib (fun ω : Bool => (ω, true)) (fun _ => true) uniformBool ∧
        ∀ (p q : Measure Bool) [SFinite q], κ false ≠ p.prod q := by
  have hci : CondIndepFun (MeasurableSpace.comap (fun _ : Bool => true) inferInstance)
      (measurable_const.comap_le) (id : Bool → Bool) (fun _ => true) uniformBool :=
    condIndepFun_const_right _ _
  have h1 := (condIndepFun_iff_condDistrib_prod_ae_eq_prod (μ := uniformBool) (U := id)
    (V := fun _ => true) measurable_id measurable_const measurable_const).1 hci
  exact ⟨hci, h1, fun z => Kernel.prod_apply _ _ z,
    exists_condDistrib_version_not_prod (μ := uniformBool) id fun _ => true⟩

end Version

end CausalInference
