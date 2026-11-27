/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Mediation.Identification
public import Mathlib.Probability.UniformOn

/-!
# Mediation: non-identification of the natural direct effect in a randomized model class

Two concrete mediation models on the eight point space `Bool × Bool × Bool` with the uniform
(product) measure. Write a point as `(A, U, V)`. In both models the treatment is the fair coin
`A`, the mediators are `M 0 = U` and `M 1 = V`, and `Y 0 m = 0`. They differ only in
`Y 1 m`: it is `1` when `m = U` in the first model and `1` when `m ≠ U` in the second.

So `Y 1 m` is coupled with the mediator `M 0 = U` of the *other* world. Since `U` is a fair coin
independent of `(A, V)`, flipping it changes no single world quantity, yet the natural direct
effect `NDE(0) = E[Y 1 (M 0) - Y 0 (M 0)]` is `1` in the first model and `0` in the second.

## Main results

* `Counterexample.map_world_eq`: for every treatment `a` and mediator value `m`, the joint law of
  `(A, M a, Y a m)` is the same in both models; `Counterexample.cde_eq`: the controlled direct
  effects agree.
* `Counterexample.map_obs_eq`: the observed law of `(A, Mobs, Yobs)` is the same in both models.
* `Counterexample.indepFun_A₁`, `Counterexample.indepFun_A₂`: in both models treatment is
  randomized, that is independent of all potential outcomes jointly.
* `Counterexample.indepFun_med₁`, `Counterexample.indepFun_med₂`, `Counterexample.cell_pos`,
  `Counterexample.cell_pos₂`: mediator ignorability given treatment and positivity of every
  observed cell hold in both models. With treatment ignorability (`indepFun_Y_A₁`,
  `indepFun_Y_A₂`, `indepFun_M_A`, `indepFun_M_A₂`) and positive arms, every single world
  hypothesis of `MediationModel.interventionalMean_eq_mediationFormula` holds in both models
  (`mediationFormula_eq_interventionalMean₁`, `mediationFormula_eq_interventionalMean₂`).
* `Counterexample.not_indepFun_cross₁`, `Counterexample.not_indepFun_cross₂`: cross world
  independence `Y 1 1 ⫫ M 0` fails in both models.
* `Counterexample.mediationFormula_sub₁`, `Counterexample.mediationFormula_sub₂`: the mediation
  formula for the pure natural direct effect is `1 / 2` in both models;
  `Counterexample.mediationFormula_sub_ne_nde₁`, `Counterexample.mediationFormula_sub_ne_nde₂`:
  it differs from the natural direct effect in both.
* `Counterexample.nde_ne`: the pure natural direct effects differ (`1` and `0`).

Conclusion. Consider the class of models with randomized treatment, mediator ignorability given
treatment, and positive observed cells. Within this class the natural direct effect is not
identified from the single world laws of `(A, M a, Y a m)` together with the observed law: two
models of the class share all of these laws and have different natural direct effects. Both
violate cross world independence, which is exactly the hypothesis of the mediation formula that
is not single world. This does not exclude identification under other single world
restrictions outside this class (for example a degenerate mediator).
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

/-! ### The hypotheses of the mediation formula in the two models -/

/-- `μ₀` is the uniform measure on the eight points of `Ω₀`. -/
theorem μ₀_eq_uniformOn : μ₀ = uniformOn Set.univ := by
  refine Measure.ext_of_singleton fun ω => ?_
  rw [uniformOn_univ, Measure.count_singleton]
  obtain ⟨a, u, v⟩ := ω
  simp only [μ₀, ← Set.singleton_prod_singleton, Measure.prod_prod, uniformOn_univ,
    Measure.count_singleton, Fintype.card_prod, Fintype.card_bool]
  norm_num [ENNReal.div_eq_inv_mul]
  rw [← ENNReal.mul_inv (by simp) (by simp), ← ENNReal.mul_inv (by simp) (by simp)]
  norm_num

/-- The probability of an event of `Ω₀` is its number of points divided by `8`. -/
theorem μ₀_real_eq (p : Ω₀ → Prop) [DecidablePred p] :
    μ₀.real {ω | p ω} = ((Finset.univ.filter p).card : ℝ) / 8 := by
  rw [μ₀_eq_uniformOn, measureReal_def, uniformOn_univ, ← Finset.coe_filter_univ,
    Measure.count_apply_finset]
  simp [ENNReal.toReal_div]

/-- Every point of `Ω₀` has probability `1 / 8`. -/
theorem μ₀_real_singleton (ω : Ω₀) : μ₀.real {ω} = 1 / 8 := by
  have h := μ₀_real_eq (· = ω)
  simp only [Set.ofPred_eq_eq_singleton, Finset.filter_eq', Finset.mem_univ, ite_true,
    Finset.card_singleton] at h
  rw [h]
  norm_num

/-- Integrals under `μ₀` are averages over the eight points. -/
theorem integral_μ₀ (f : Ω₀ → ℝ) : ∫ ω, f ω ∂μ₀ = (∑ ω, f ω) / 8 := by
  rw [integral_fintype Integrable.of_finite, Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [μ₀_real_singleton, smul_eq_mul]
  ring

/-- The probability of an event of `Ω₀` is the average of its indicator over the eight points. -/
theorem μ₀_real_eq_sum (s : Set Ω₀) : μ₀.real s = (∑ ω, s.indicator (1 : Ω₀ → ℝ) ω) / 8 := by
  rw [← integral_μ₀, integral_indicator_one (Set.toFinite s).measurableSet]

/-- An event of `Ω₀` containing a point has positive probability. -/
theorem μ₀_ne_zero_of_mem {s : Set Ω₀} {ω : Ω₀} (h : ω ∈ s) : μ₀ s ≠ 0 := by
  have h1 : μ₀ {ω} ≠ 0 := by simp [μ₀_eq_uniformOn, uniformOn_univ]
  exact fun h0 => h1 (measure_mono_null (Set.singleton_subset_iff.2 h) h0)

/-- Every permutation of `Ω₀` preserves independence under `μ₀`. -/
theorem indepFun_comp_equiv {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω₀ → β} {g : Ω₀ → γ} (e : Ω₀ ≃ Ω₀) (h : IndepFun f g μ₀) :
    IndepFun (f ∘ e) (g ∘ e) μ₀ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have h' := h s t hs ht
  rw [← map_equiv_μ₀ e] at h'
  simp only [Measure.map_apply (measurable_of_finite e) (Set.toFinite _).measurableSet] at h'
  exact h'

/-- If `A` is independent of the pair `(X, Z)` and `X` is independent of `Z`, then `X` and `Z`
remain independent given `A = a`, for `P(A = a) > 0`. -/
theorem indepFun_cond_of_indepFun_pair {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure Ω} [IsProbabilityMeasure μ] {A : Ω → Bool} {X : Ω → β}
    {Z : Ω → γ} (hA : Measurable A) (hAXZ : IndepFun A (fun ω => (X ω, Z ω)) μ)
    (hXZ : IndepFun X Z μ) {a : Bool} (hpos : μ (A ⁻¹' {a}) ≠ 0) :
    IndepFun X Z μ[|A ⁻¹' {a}] := by
  have hSA : MeasurableSet (A ⁻¹' {a}) := hA (measurableSet_singleton a)
  have key : ∀ S : Set (β × γ), MeasurableSet S →
      μ[|A ⁻¹' {a}] ((fun ω => (X ω, Z ω)) ⁻¹' S) = μ ((fun ω => (X ω, Z ω)) ⁻¹' S) := by
    intro S hS
    rw [cond_apply hSA, hAXZ.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton a) hS,
      ← mul_assoc, ENNReal.inv_mul_cancel hpos (measure_ne_top _ _), one_mul]
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have e1 : X ⁻¹' s ∩ Z ⁻¹' t = (fun ω => (X ω, Z ω)) ⁻¹' (s ×ˢ t) := rfl
  have e2 : X ⁻¹' s = (fun ω => (X ω, Z ω)) ⁻¹' (s ×ˢ Set.univ) := by ext; simp
  have e3 : Z ⁻¹' t = (fun ω => (X ω, Z ω)) ⁻¹' (Set.univ ×ˢ t) := by ext; simp
  rw [e1, e2, e3, key _ (hs.prod ht), key _ (hs.prod MeasurableSet.univ),
    key _ (MeasurableSet.univ.prod ht), ← e1, ← e2, ← e3,
    hXZ.measure_inter_preimage_eq_mul _ _ hs ht]

/-- Under `μ₀` the treatment coordinate `A` is independent of the pair `(U, V)`. -/
theorem indepFun_A_UV : IndepFun (fun ω : Ω₀ => ω.1) (fun ω => ω.2) μ₀ := by
  unfold μ₀
  exact indepFun_prod measurable_id measurable_id

/-- The permutation of `Ω₀` that exchanges `A` and `U`. -/
def swapAU : Ω₀ ≃ Ω₀ where
  toFun ω := (ω.2.1, ω.1, ω.2.2)
  invFun ω := (ω.2.1, ω.1, ω.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Under `μ₀` the coordinates `U` and `V` are independent. -/
theorem indepFun_U_V : IndepFun (fun ω : Ω₀ => ω.2.1) (fun ω => ω.2.2) μ₀ :=
  indepFun_comp_equiv swapAU (indepFun_A_UV.comp measurable_id measurable_snd)

/-- Given `A = a`, the coordinates `U` and `V` are independent. -/
theorem indepFun_U_V_cond (a : Bool) :
    IndepFun (fun ω : Ω₀ => ω.2.1) (fun ω => ω.2.2) μ₀[|(fun ω : Ω₀ => ω.1) ⁻¹' {a}] :=
  indepFun_cond_of_indepFun_pair measurable_fst indepFun_A_UV indepFun_U_V
    (μ₀_ne_zero_of_mem (ω := (a, true, true)) rfl)

/-- Cross world independence `Y 1 1 ⫫ M 0` fails in the first model:
`P(Y 1 1 = 1, M 0 = 1) = 1 / 2`, while `P(Y 1 1 = 1) P(M 0 = 1) = 1 / 4`. -/
theorem not_indepFun_cross₁ : ¬ IndepFun (model₁.Y true true) (model₁.M false) μ₀ := by
  intro h
  have h' := congrArg ENNReal.toReal (h.measure_inter_preimage_eq_mul {1} {true}
    (measurableSet_singleton _) (measurableSet_singleton _))
  rw [ENNReal.toReal_mul] at h'
  simp only [← measureReal_def, μ₀_real_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool] at h'
  simp [Set.indicator, model₁] at h'
  norm_num at h'

/-- Cross world independence `Y 1 1 ⫫ M 0` fails in the second model:
`P(Y 1 1 = 1, M 0 = 1) = 0`, while `P(Y 1 1 = 1) P(M 0 = 1) = 1 / 4`. -/
theorem not_indepFun_cross₂ : ¬ IndepFun (model₂.Y true true) (model₂.M false) μ₀ := by
  intro h
  have h' := congrArg ENNReal.toReal (h.measure_inter_preimage_eq_mul {1} {true}
    (measurableSet_singleton _) (measurableSet_singleton _))
  rw [ENNReal.toReal_mul] at h'
  simp only [← measureReal_def, μ₀_real_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool] at h'
  simp [Set.indicator, model₂] at h'

/-- Treatment ignorability for the outcomes in the first model: `Y a m ⫫ A`. -/
theorem indepFun_Y_A₁ (a m : Bool) : IndepFun (model₁.Y a m) model₁.A μ₀ :=
  indepFun_A_UV.symm.comp (measurable_of_finite fun p : Bool × Bool =>
    if a then (if m = p.1 then (1 : ℝ) else 0) else 0) measurable_id

/-- Treatment ignorability for the outcomes in the second model: `Y a m ⫫ A`. -/
theorem indepFun_Y_A₂ (a m : Bool) : IndepFun (model₂.Y a m) model₂.A μ₀ :=
  indepFun_A_UV.symm.comp (measurable_of_finite fun p : Bool × Bool =>
    if a then (if m = p.1 then (0 : ℝ) else 1) else 0) measurable_id

/-- Treatment ignorability for the mediators (the same in both models): `M a ⫫ A`. -/
theorem indepFun_M_A (a : Bool) : IndepFun (model₁.M a) model₁.A μ₀ :=
  indepFun_A_UV.symm.comp (measurable_of_finite fun p : Bool × Bool => if a then p.2 else p.1)
    measurable_id

/-- Mediator ignorability given treatment in the first model: `Y a m ⫫ M a` under
`μ₀[|A = a]`. -/
theorem indepFun_med₁ (a m : Bool) :
    IndepFun (model₁.Y a m) (model₁.M a) μ₀[|model₁.A ⁻¹' {a}] := by
  cases a
  · have : IsProbabilityMeasure μ₀[|model₁.A ⁻¹' {false}] :=
      cond_isProbabilityMeasure (μ₀_ne_zero_of_mem (ω := (false, true, true)) rfl)
    exact indepFun_const_left (0 : ℝ) _
  · exact (indepFun_U_V_cond true).comp
      (measurable_of_finite fun u : Bool => if m = u then (1 : ℝ) else 0) measurable_id

/-- Mediator ignorability given treatment in the second model: `Y a m ⫫ M a` under
`μ₀[|A = a]`. -/
theorem indepFun_med₂ (a m : Bool) :
    IndepFun (model₂.Y a m) (model₂.M a) μ₀[|model₂.A ⁻¹' {a}] := by
  cases a
  · have : IsProbabilityMeasure μ₀[|model₂.A ⁻¹' {false}] :=
      cond_isProbabilityMeasure (μ₀_ne_zero_of_mem (ω := (false, true, true)) rfl)
    exact indepFun_const_left (0 : ℝ) _
  · exact (indepFun_U_V_cond true).comp
      (measurable_of_finite fun u : Bool => if m = u then (0 : ℝ) else 1) measurable_id

/-- Positivity of every observed cell `A = a, Mobs = m` (the same in both models). -/
theorem cell_pos (a m : Bool) : μ₀ (model₁.A ⁻¹' {a} ∩ model₁.Mobs ⁻¹' {m}) ≠ 0 :=
  μ₀_ne_zero_of_mem (ω := (a, m, m)) (by cases a <;> simp [model₁, MediationModel.Mobs])

/-- Positivity of both treatment arms. -/
theorem arm_pos (a : Bool) : μ₀ (model₁.A ⁻¹' {a}) ≠ 0 :=
  μ₀_ne_zero_of_mem (ω := (a, true, true)) rfl

/-- In the first model every single world hypothesis of
`MediationModel.interventionalMean_eq_mediationFormula` holds, so the mediation formula equals
the interventional mean. -/
theorem mediationFormula_eq_interventionalMean₁ (a a' : Bool) :
    model₁.mediationFormula μ₀ a a' = model₁.interventionalMean μ₀ a a' :=
  (model₁.interventionalMean_eq_mediationFormula (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (fun _ _ => Integrable.of_finite)
    (fun m _ => indepFun_Y_A₁ a m) (indepFun_M_A a') (fun m _ => indepFun_med₁ a m)
    (arm_pos a') (fun m _ => cell_pos a m)).symm

/-- Treatment ignorability for the mediators in the second model: `M a ⫫ A`. -/
theorem indepFun_M_A₂ (a : Bool) : IndepFun (model₂.M a) model₂.A μ₀ :=
  indepFun_M_A a

/-- Positivity of every observed cell `A = a, Mobs = m` in the second model. -/
theorem cell_pos₂ (a m : Bool) : μ₀ (model₂.A ⁻¹' {a} ∩ model₂.Mobs ⁻¹' {m}) ≠ 0 :=
  cell_pos a m

/-- Positivity of both treatment arms in the second model. -/
theorem arm_pos₂ (a : Bool) : μ₀ (model₂.A ⁻¹' {a}) ≠ 0 :=
  arm_pos a

/-- In the second model every single world hypothesis of
`MediationModel.interventionalMean_eq_mediationFormula` holds, so the mediation formula equals
the interventional mean. -/
theorem mediationFormula_eq_interventionalMean₂ (a a' : Bool) :
    model₂.mediationFormula μ₀ a a' = model₂.interventionalMean μ₀ a a' :=
  (model₂.interventionalMean_eq_mediationFormula (measurable_of_finite _)
    (measurable_of_finite _) (measurable_of_finite _) (fun _ _ => Integrable.of_finite)
    (fun m _ => indepFun_Y_A₂ a m) (indepFun_M_A₂ a') (fun m _ => indepFun_med₂ a m)
    (arm_pos₂ a') (fun m _ => cell_pos₂ a m)).symm

/-- The mediation formula is the same in both models, since their observed laws agree. -/
theorem mediationFormula_eq (a a' : Bool) :
    model₁.mediationFormula μ₀ a a' = model₂.mediationFormula μ₀ a a' :=
  model₁.mediationFormula_eq_of_map_eq model₂ a a' (measurable_of_finite _).aemeasurable
    (measurable_of_finite _).aemeasurable map_obs_eq

/-- The mediation formula for treatment `1` and mediator world `0` is `1 / 2` in the first
model. -/
theorem mediationFormula₁_true_false : model₁.mediationFormula μ₀ true false = 1 / 2 := by
  rw [mediationFormula_eq_interventionalMean₁, MediationModel.interventionalMean]
  simp only [integral_μ₀, μ₀_real_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [Set.indicator, model₁]
  norm_num

/-- The mediation formula for treatment `0` and mediator world `0` is `0` in the first model. -/
theorem mediationFormula₁_false_false : model₁.mediationFormula μ₀ false false = 0 := by
  rw [mediationFormula_eq_interventionalMean₁, MediationModel.interventionalMean]
  simp [model₁]

/-- In the first model the mediation formula gives `1 / 2` for the pure natural direct
effect. -/
theorem mediationFormula_sub₁ :
    model₁.mediationFormula μ₀ true false - model₁.mediationFormula μ₀ false false = 1 / 2 := by
  rw [mediationFormula₁_true_false, mediationFormula₁_false_false, sub_zero]

/-- In the second model the mediation formula gives `1 / 2` for the pure natural direct
effect. -/
theorem mediationFormula_sub₂ :
    model₂.mediationFormula μ₀ true false - model₂.mediationFormula μ₀ false false = 1 / 2 := by
  rw [← mediationFormula_eq, ← mediationFormula_eq, mediationFormula_sub₁]

/-- The mediation formula differs from the natural direct effect in the first model
(`1 / 2` against `1`). -/
theorem mediationFormula_sub_ne_nde₁ :
    model₁.mediationFormula μ₀ true false - model₁.mediationFormula μ₀ false false ≠
      model₁.nde μ₀ false := by
  rw [mediationFormula_sub₁, nde₁]
  norm_num

/-- The mediation formula differs from the natural direct effect in the second model
(`1 / 2` against `0`). -/
theorem mediationFormula_sub_ne_nde₂ :
    model₂.mediationFormula μ₀ true false - model₂.mediationFormula μ₀ false false ≠
      model₂.nde μ₀ false := by
  rw [mediationFormula_sub₂, nde₂]
  norm_num

/-- The controlled direct effects of the two models agree. -/
theorem cde_eq (m : Bool) : model₁.cde μ₀ m = model₂.cde μ₀ m := by
  simp only [MediationModel.cde, integral_μ₀, Fintype.sum_prod_type, Fintype.sum_bool]
  cases m <;> simp [model₁, model₂]

end Counterexample

end Mediation

end CausalInference
