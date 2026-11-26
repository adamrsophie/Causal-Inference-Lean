/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Mediation.Basic
public import Mathlib.Probability.UniformOn

/-!
# Mediation: natural effects are not identified without cross world assumptions

Two concrete mediation models on the eight point space `Bool × Bool × Bool` with the uniform
(product) measure. Write a point as `(A, U, V)`. In both models the treatment is the fair coin
`A`, the mediators are `M 0 = U` and `M 1 = V`, and `Y 0 m = 0`. They differ only in
`Y 1 m`: it is `1` when `m = U` in the first model and `1` when `m ≠ U` in the second.

So `Y 1 m` is coupled with the mediator `M 0 = U` of the *other* world. Since `U` is a fair coin
independent of `(A, V)`, flipping it changes no single world quantity, yet the natural direct
effect `NDE(0) = E[Y 1 (M 0) - Y 0 (M 0)]` is `1` in the first model and `0` in the second.

## Main results

* `Counterexample.map_world_eq`: for every treatment `a` and mediator value `m`, the joint law of
  `(A, M a, Y a m)` is the same in both models.
* `Counterexample.map_obs_eq`: the observed law of `(A, Mobs, Yobs)` is the same in both models.
* `Counterexample.indepFun_A₁`, `Counterexample.indepFun_A₂`: in both models treatment is
  randomized, that is independent of all potential outcomes jointly.
* `Counterexample.nde_ne`: the pure natural direct effects differ (`1` and `0`).

Hence no assumption about single world laws, and no observational or interventional data, can
identify the natural direct effect; a cross world assumption such as `Y a m ⫫ M a'` is needed.
Both models violate it, since `Y 1 m` is a function of `M 0`; this violation is
evident from the definitions and is not stated as a separate theorem here.
-/

@[expose] public section

namespace CausalInference

namespace Mediation

namespace Counterexample

open MeasureTheory ProbabilityTheory

/-- The sample space: points `(A, U, V)` of three bits. -/
abbrev Ω₀ : Type := Bool × Bool × Bool

/-- The uniform measure on `Ω₀`, written as a product of three fair coins. -/
noncomputable def μ₀ : Measure Ω₀ :=
  (uniformOn Set.univ : Measure Bool).prod
    ((uniformOn Set.univ : Measure Bool).prod (uniformOn Set.univ : Measure Bool))

instance : IsProbabilityMeasure μ₀ := by
  unfold μ₀
  infer_instance

/-- The first model: `A`, `M 0 = U`, `M 1 = V`, `Y 0 m = 0`, and `Y 1 m = 1` exactly when
`m = U`. -/
def model₁ : MediationModel Ω₀ Bool where
  A ω := ω.1
  M a ω := if a then ω.2.2 else ω.2.1
  Y a m ω := if a then (if m = ω.2.1 then 1 else 0) else 0

/-- The second model: the same as `model₁` except that `Y 1 m = 1` exactly when `m ≠ U`. -/
def model₂ : MediationModel Ω₀ Bool where
  A ω := ω.1
  M a ω := if a then ω.2.2 else ω.2.1
  Y a m ω := if a then (if m = ω.2.1 then 0 else 1) else 0

/-- Every point of `Ω₀` has the same mass under `μ₀`. -/
theorem μ₀_singleton_eq (ω ω' : Ω₀) : μ₀ {ω} = μ₀ {ω'} := by
  obtain ⟨a, u, v⟩ := ω
  obtain ⟨a', u', v'⟩ := ω'
  simp only [μ₀, ← Set.singleton_prod_singleton, Measure.prod_prod, uniformOn_univ,
    Measure.count_singleton]

/-- Every permutation of `Ω₀` preserves `μ₀`. -/
theorem map_equiv_μ₀ (e : Ω₀ ≃ Ω₀) : μ₀.map e = μ₀ := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [Measure.map_apply (measurable_of_finite e) (measurableSet_singleton x)]
  have : e ⁻¹' {x} = {e.symm x} := by
    ext ω
    simp [Equiv.eq_symm_apply]
  rw [this, μ₀_singleton_eq]

/-- If `g = f ∘ e` for a permutation `e` of `Ω₀`, then `f` and `g` have the same law. -/
theorem map_eq_of_eq_comp {β : Type*} [MeasurableSpace β] {f g : Ω₀ → β} (e : Ω₀ ≃ Ω₀)
    (h : g = f ∘ e) : μ₀.map f = μ₀.map g := by
  rw [h, ← Measure.map_map (measurable_of_finite f) (measurable_of_finite e), map_equiv_μ₀]

/-- The permutation of `Ω₀` that flips `U`. -/
def flipU : Ω₀ ≃ Ω₀ where
  toFun ω := (ω.1, !ω.2.1, ω.2.2)
  invFun ω := (ω.1, !ω.2.1, ω.2.2)
  left_inv ω := by simp
  right_inv ω := by simp

/-- The permutation of `Ω₀` that flips `U` on the event `A = 1` only. -/
def flipUOnTreated : Ω₀ ≃ Ω₀ where
  toFun ω := (ω.1, if ω.1 then !ω.2.1 else ω.2.1, ω.2.2)
  invFun ω := (ω.1, if ω.1 then !ω.2.1 else ω.2.1, ω.2.2)
  left_inv := by rintro ⟨a, u, v⟩; cases a <;> simp
  right_inv := by rintro ⟨a, u, v⟩; cases a <;> simp

/-- Same single world laws: for every treatment `a` and mediator value `m`, the joint law of
`(A, M a, Y a m)` under `μ₀` is the same in both models. -/
theorem map_world_eq (a m : Bool) :
    μ₀.map (fun ω => (model₁.A ω, model₁.M a ω, model₁.Y a m ω)) =
      μ₀.map (fun ω => (model₂.A ω, model₂.M a ω, model₂.Y a m ω)) := by
  cases a
  · rfl
  · refine map_eq_of_eq_comp flipU ?_
    funext ⟨a₀, u, v⟩
    cases m <;> cases u <;> simp [model₁, model₂, flipU]

/-- Same observed law: the joint law of `(A, Mobs, Yobs)` under `μ₀` is the same in both
models. -/
theorem map_obs_eq :
    μ₀.map (fun ω => (model₁.A ω, model₁.Mobs ω, model₁.Yobs ω)) =
      μ₀.map (fun ω => (model₂.A ω, model₂.Mobs ω, model₂.Yobs ω)) := by
  refine map_eq_of_eq_comp flipUOnTreated ?_
  funext ⟨a, u, v⟩
  cases a <;> cases u <;> cases v <;>
    simp [model₁, model₂, flipUOnTreated, MediationModel.Mobs, MediationModel.Yobs]

/-- Randomized treatment in the first model: `A` is independent of the whole vector of potential
outcomes `(M, Y)`. -/
theorem indepFun_A₁ :
    IndepFun model₁.A (fun ω => (fun a => model₁.M a ω, fun a m => model₁.Y a m ω)) μ₀ :=
  indepFun_prod measurable_id (measurable_of_finite fun ω : Bool × Bool =>
    ((fun a : Bool => if a then ω.2 else ω.1),
      fun (a m : Bool) => if a then (if m = ω.1 then (1 : ℝ) else 0) else 0))

/-- Randomized treatment in the second model: `A` is independent of the whole vector of potential
outcomes `(M, Y)`. -/
theorem indepFun_A₂ :
    IndepFun model₂.A (fun ω => (fun a => model₂.M a ω, fun a m => model₂.Y a m ω)) μ₀ :=
  indepFun_prod measurable_id (measurable_of_finite fun ω : Bool × Bool =>
    ((fun a : Bool => if a then ω.2 else ω.1),
      fun (a m : Bool) => if a then (if m = ω.1 then (0 : ℝ) else 1) else 0))

/-- The pure natural direct effect of the first model is `1`. -/
theorem nde₁ : model₁.nde μ₀ false = 1 := by
  simp [MediationModel.nde, MediationModel.nested, model₁]

/-- The pure natural direct effect of the second model is `0`. -/
theorem nde₂ : model₂.nde μ₀ false = 0 := by
  simp [MediationModel.nde, MediationModel.nested, model₂]

/-- The natural direct effects of the two models differ, although they have randomized treatment,
the same single world laws (`map_world_eq`) and the same observed law (`map_obs_eq`). -/
theorem nde_ne : model₁.nde μ₀ false ≠ model₂.nde μ₀ false := by
  rw [nde₁, nde₂]
  exact one_ne_zero

end Counterexample

end Mediation

end CausalInference
