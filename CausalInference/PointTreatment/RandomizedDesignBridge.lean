/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.WeightingConsistency
public import CausalInference.Designs.Randomized.Bernoulli
public import CausalInference.Designs.Randomized.Complete

/-!
# Point treatment: from finite population designs to a randomized superpopulation

A finite population design (`CausalInference.Randomized.Design`) draws an assignment vector
`a : ι → Bool` for the units of a finite population `ι`. Drawing in addition one unit `i`
uniformly at random gives a probability measure `designUnitMeasure` on `ι × (ι → Bool)`, the
finite weighted sum of Dirac masses `∑_{i, a} N⁻¹ w(a) δ_{(i, a)}` over the units and the
assignments of the support. On this space the treatment of the drawn unit is `A (i, a) = a i`,
and covariates and potential outcomes of the population become functions of the drawn unit.

If every unit has the same inclusion probability `p`, the treatment of the drawn unit is
independent of the drawn unit (`indepFun_unitTreatment_unit`) and has probability `p`
(`designUnitMeasure_real_unitTreatment`). So it is independent of the unit's covariates and
potential outcomes, which is the hypothesis of `indicatorIgnorable_of_indepFun` and of the trial
consistency theorems. The Bernoulli design (`bernoulliDesign_inclusionProb`) and the completely
randomized design with `n₁` treated of `N` (`completeDesign_inclusionProb`, which rests on the
exchangeability of that design) both have constant inclusion probabilities.

The design objects used are `Design` (its `support`, `weight`, `weight_nonneg`, `sum_weight`),
`Design.inclusionProb`, `treatInd`, `bernoulliDesign` with `bernoulliDesign_inclusionProb`, and
`completeDesign` with `completeDesign_inclusionProb`.

## Main definitions

* `designUnitMass`, `designUnitMeasure`: the uniform unit and the drawn assignment.
* `unitTreatment`: the treatment `a i` of the drawn unit.

## Main results

* `designUnitMeasure_apply`, `isProbabilityMeasure_designUnitMeasure`.
* `indepFun_unitTreatment_unit`, `designUnitMeasure_real_unitTreatment`: constant inclusion
  probability gives independence and the treatment probability.
* `indepFun_unitTreatment_of_inclusionProb`, `indicatorIgnorable_designUnitMeasure`: independence of
  the covariates and potential outcomes, and ignorability given any unit covariate.
* `indepFun_unitTreatment_bernoulli`, `indepFun_unitTreatment_complete`: the two designs.
* `isConsistent_sampleNaiveContrast_bernoulli`, `isConsistent_sampleNaiveContrast_complete`:
  the difference in arm means of an i.i.d. sample from either superpopulation is consistent
  for its average effect.
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData Finset Randomized

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mass of the pair `(i, a)`: `N⁻¹ w(a)` for an assignment of the support, `0` otherwise. -/
noncomputable def designUnitMass (d : Design ι) (x : ι × (ι → Bool)) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * if x.2 ∈ d.support then d.weight x.2 else 0

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- **The uniform unit and the drawn assignment**: `∑_{i, a} N⁻¹ w(a) δ_{(i, a)}`. -/
noncomputable def designUnitMeasure (d : Design ι) : Measure (ι × (ι → Bool)) :=
  ∑ x, ENNReal.ofReal (designUnitMass d x) • Measure.dirac x

/-- The treatment of the drawn unit. -/
def unitTreatment (x : ι × (ι → Bool)) : Bool := x.2 x.1

omit [DecidableEq ι] in
theorem designUnitMass_nonneg (d : Design ι) (x : ι × (ι → Bool)) : 0 ≤ designUnitMass d x := by
  unfold designUnitMass
  split_ifs with h
  · exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (d.weight_nonneg _ h)
  · simp

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem designUnitMeasure_apply (d : Design ι) (S : Set (ι × (ι → Bool))) :
    designUnitMeasure d S = ENNReal.ofReal (∑ x, S.indicator (designUnitMass d) x) := by
  classical
  rw [designUnitMeasure, FunLike.coe_sum, Finset.sum_apply,
    ENNReal.ofReal_sum_of_nonneg fun x _ =>
      Set.indicator_nonneg (fun y _ => designUnitMass_nonneg d y) x]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases hx : x ∈ S <;> simp [hx]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The weight extended by `0` outside the support sums to one. -/
theorem design_sum_ite_weight (d : Design ι) :
    ∑ a, (if a ∈ d.support then d.weight a else 0) = 1 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, d.sum_weight]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The inclusion probability as a sum over all assignments. -/
theorem design_inclusionProb_eq_sum (d : Design ι) (i : ι) :
    d.inclusionProb i = ∑ a, (if a ∈ d.support then d.weight a else 0) * treatInd a i := by
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  rfl

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The mass of a rectangle `{x.1 ∈ t, x.2 x.1 ∈ s}` when every unit has inclusion
probability `p`: `N⁻¹ |t| (1{1 ∈ s} p + 1{0 ∈ s} (1 - p))`. -/
theorem designUnitMass_sum_indicator_rect (d : Design ι) {p : ℝ} (hp : ∀ i, d.inclusionProb i = p)
    (s : Set Bool) (t : Set ι) :
    ∑ x, {x : ι × (ι → Bool) | x.1 ∈ t ∧ x.2 x.1 ∈ s}.indicator (designUnitMass d) x =
      (Fintype.card ι : ℝ)⁻¹ * ((∑ i, t.indicator (fun _ => (1 : ℝ)) i) *
        (s.indicator (fun _ => (1 : ℝ)) true * p +
          s.indicator (fun _ => (1 : ℝ)) false * (1 - p))) := by
  classical
  set w' : (ι → Bool) → ℝ := fun a => if a ∈ d.support then d.weight a else 0
  have hb : ∀ (a : ι → Bool) (i : ι), s.indicator (fun _ => (1 : ℝ)) (a i) =
      s.indicator (fun _ => (1 : ℝ)) true * treatInd a i +
        s.indicator (fun _ => (1 : ℝ)) false * (1 - treatInd a i) := fun a i => by
    cases h : a i <;> simp [treatInd, h]
  have hcell : ∀ i, ∑ a, w' a * s.indicator (fun _ => (1 : ℝ)) (a i) =
      s.indicator (fun _ => (1 : ℝ)) true * p + s.indicator (fun _ => (1 : ℝ)) false * (1 - p) :=
    fun i => by
      simp only [hb, mul_add, Finset.sum_add_distrib, mul_sub, mul_one, Finset.sum_sub_distrib]
      have h1 : ∑ a, w' a * (s.indicator (fun _ => (1 : ℝ)) true * treatInd a i) =
          s.indicator (fun _ => (1 : ℝ)) true * p := by
        rw [← hp i, design_inclusionProb_eq_sum d, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      have h2 : ∑ a, w' a * (s.indicator (fun _ => (1 : ℝ)) false * treatInd a i) =
          s.indicator (fun _ => (1 : ℝ)) false * p := by
        rw [← hp i, design_inclusionProb_eq_sum d, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      have h3 : ∑ a, w' a * s.indicator (fun _ => (1 : ℝ)) false =
          s.indicator (fun _ => (1 : ℝ)) false := by
        rw [← Finset.sum_mul, design_sum_ite_weight d, one_mul]
      rw [h1, h2, h3]
  have hx : ∀ i a,
      {x : ι × (ι → Bool) | x.1 ∈ t ∧ x.2 x.1 ∈ s}.indicator (designUnitMass d) (i, a) =
      (Fintype.card ι : ℝ)⁻¹ * (t.indicator (fun _ => (1 : ℝ)) i *
        (w' a * s.indicator (fun _ => (1 : ℝ)) (a i))) := fun i a => by
    by_cases hi : i ∈ t <;> by_cases ha : a i ∈ s <;>
      simp [designUnitMass, w', hi, ha]
  rw [Fintype.sum_prod_type]
  simp only [hx, ← Finset.mul_sum, hcell, ← Finset.sum_mul]

variable (d : Design ι)

theorem isProbabilityMeasure_designUnitMeasure [Nonempty ι] :
    IsProbabilityMeasure (designUnitMeasure d) := by
  constructor
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [designUnitMeasure_apply d, Set.indicator_univ, Fintype.sum_prod_type]
  simp only [designUnitMass, ← Finset.mul_sum, design_sum_ite_weight d, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [mul_inv_cancel₀ hN, ENNReal.ofReal_one]

/-- **Constant inclusion probability gives independence**: if every unit has inclusion
probability `p`, the treatment of the drawn unit is independent of the drawn unit. -/
theorem indepFun_unitTreatment_unit [Nonempty ι] {p : ℝ} (hp : ∀ i, d.inclusionProb i = p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IndepFun unitTreatment Prod.fst (designUnitMeasure d) := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t _ _
  have e1 : unitTreatment ⁻¹' s ∩ Prod.fst ⁻¹' t =
      {x : ι × (ι → Bool) | x.1 ∈ t ∧ x.2 x.1 ∈ s} := by
    ext x; simp [unitTreatment, and_comm]
  have e2 : unitTreatment ⁻¹' s = {x : ι × (ι → Bool) | x.1 ∈ Set.univ ∧ x.2 x.1 ∈ s} := by
    ext x; simp [unitTreatment]
  have e3 : Prod.fst ⁻¹' t = {x : ι × (ι → Bool) | x.1 ∈ t ∧ x.2 x.1 ∈ Set.univ} := by
    ext x; simp
  have hc : 0 ≤ s.indicator (fun _ => (1 : ℝ)) true * p +
      s.indicator (fun _ => (1 : ℝ)) false * (1 - p) :=
    add_nonneg (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) hp0)
      (mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (by linarith))
  rw [e1, e2, e3, designUnitMeasure_apply, designUnitMeasure_apply, designUnitMeasure_apply,
    designUnitMass_sum_indicator_rect d hp, designUnitMass_sum_indicator_rect d hp,
    designUnitMass_sum_indicator_rect d hp, ← ENNReal.ofReal_mul (by
      simp only [Set.indicator_univ, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) hc))]
  congr 1
  simp only [Set.indicator_univ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, one_mul]
  field_simp
  ring

/-- If every unit has inclusion probability `p`, the drawn unit is treated with probability
`p`. -/
theorem designUnitMeasure_real_unitTreatment [Nonempty ι] {p : ℝ}
    (hp : ∀ i, d.inclusionProb i = p) (hp0 : 0 ≤ p) :
    (designUnitMeasure d).real (unitTreatment ⁻¹' {true}) = p := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e2 : unitTreatment ⁻¹' {true} =
      {x : ι × (ι → Bool) | x.1 ∈ Set.univ ∧ x.2 x.1 ∈ ({true} : Set Bool)} := by
    ext x; simp [unitTreatment]
  rw [measureReal_def, e2, designUnitMeasure_apply, designUnitMass_sum_indicator_rect d hp]
  simp only [Set.indicator_univ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Set.indicator_of_mem (Set.mem_singleton true),
    Set.indicator_of_notMem (show false ∉ ({true} : Set Bool) by simp), zero_mul, add_zero, one_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul, ENNReal.toReal_ofReal hp0]

variable {𝒲 : Type*} [MeasurableSpace 𝒲]

/-- **The treatment of the drawn unit is independent of its covariate and potential
outcomes** when every unit has inclusion probability `p`: for unit covariates `Wu` and unit
potential outcomes `Yu`, `A ⫫ (W, (Y(0), Y(1)))` on the superpopulation `designUnitMeasure d`. -/
theorem indepFun_unitTreatment_of_inclusionProb [Nonempty ι] {p : ℝ}
    (hp : ∀ i, d.inclusionProb i = p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Wu : ι → 𝒲)
    (Yu : Bool → ι → ℝ) :
    IndepFun unitTreatment (fun x : ι × (ι → Bool) =>
      (Wu x.1, potentialPair (fun b x => Yu b x.1) x)) (designUnitMeasure d) :=
  (indepFun_unitTreatment_unit d hp hp0 hp1).comp (φ := id)
    (ψ := fun i => (Wu i, (Yu false i, Yu true i))) measurable_id Measurable.of_discrete

/-- **A design with constant inclusion probability is ignorable given any unit covariate**, in
the indicator form, on the superpopulation `designUnitMeasure d`. -/
theorem indicatorIgnorable_designUnitMeasure [Nonempty ι] {p : ℝ}
    (hp : ∀ i, d.inclusionProb i = p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Wu : ι → 𝒲)
    (Yu : Bool → ι → ℝ) :
    IndicatorIgnorable (designUnitMeasure d) unitTreatment (fun x => Wu x.1)
      (fun b x => Yu b x.1) :=
  have := isProbabilityMeasure_designUnitMeasure d
  indicatorIgnorable_of_indepFun Measurable.of_discrete Measurable.of_discrete
    (fun _ => Measurable.of_discrete) (indepFun_unitTreatment_of_inclusionProb d hp hp0 hp1 Wu Yu)

/-- **The Bernoulli design**: with treatment probability `p`, the treatment of the drawn unit is
independent of its covariate and potential outcomes and has probability `p`. -/
theorem indepFun_unitTreatment_bernoulli [Nonempty ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Wu : ι → 𝒲) (Yu : Bool → ι → ℝ) :
    IndepFun unitTreatment (fun x : ι × (ι → Bool) =>
        (Wu x.1, potentialPair (fun b x => Yu b x.1) x))
        (designUnitMeasure (bernoulliDesign (ι := ι) p hp0 hp1)) ∧
      (designUnitMeasure (bernoulliDesign (ι := ι) p hp0 hp1)).real
        (unitTreatment ⁻¹' {true}) = p :=
  ⟨indepFun_unitTreatment_of_inclusionProb _ (bernoulliDesign_inclusionProb p hp0 hp1) hp0 hp1
    Wu Yu, designUnitMeasure_real_unitTreatment _ (bernoulliDesign_inclusionProb p hp0 hp1) hp0⟩

/-- **The completely randomized design**: with `n₁` of the `N` units treated, the treatment of
the drawn unit is independent of its covariate and potential outcomes and has probability
`n₁ / N`. -/
theorem indepFun_unitTreatment_complete [Nonempty ι] {n₁ : ℕ} (h : n₁ ≤ Fintype.card ι)
    (Wu : ι → 𝒲) (Yu : Bool → ι → ℝ) :
    IndepFun unitTreatment (fun x : ι × (ι → Bool) =>
        (Wu x.1, potentialPair (fun b x => Yu b x.1) x))
        (designUnitMeasure (completeDesign (ι := ι) n₁ h)) ∧
      (designUnitMeasure (completeDesign (ι := ι) n₁ h)).real (unitTreatment ⁻¹' {true}) =
        n₁ / Fintype.card ι := by
  have hN : 0 < Fintype.card ι := Fintype.card_pos
  have hp := completeDesign_inclusionProb n₁ h hN
  have hp0 : (0 : ℝ) ≤ n₁ / Fintype.card ι := by positivity
  have hp1 : (n₁ : ℝ) / Fintype.card ι ≤ 1 :=
    (div_le_one (Nat.cast_pos.2 hN)).2 (Nat.cast_le.2 h)
  exact ⟨indepFun_unitTreatment_of_inclusionProb _ hp hp0 hp1 Wu Yu,
    designUnitMeasure_real_unitTreatment _ hp hp0⟩

/-- **The difference in arm means under a Bernoulli superpopulation is consistent.** For an
i.i.d. sample of the observed data of a unit drawn uniformly together with a Bernoulli
assignment with probability `0 < p < 1`, the difference in arm means is consistent for the
average effect `E[Y(1) - Y(0)]` of the drawn unit. -/
theorem isConsistent_sampleNaiveContrast_bernoulli [Nonempty ι] {Ξ : Type*}
    {mΞ : MeasurableSpace Ξ} {P : Measure Ξ} [IsProbabilityMeasure P] {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (Wu : ι → 𝒲) (Yu : Bool → ι → ℝ) {O : ℕ → Ξ → 𝒲 × Bool × ℝ}
    (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) =
      (designUnitMeasure (bernoulliDesign (ι := ι) p hp0.le hp1.le)).map fun x =>
      (Wu x.1, unitTreatment x, obsOutcome unitTreatment (fun b x => Yu b x.1) x)) :
    IsConsistent (sampleNaiveContrast O)
      (ate (designUnitMeasure (bernoulliDesign (ι := ι) p hp0.le hp1.le))
        fun b x => Yu b x.1) P := by
  have := isProbabilityMeasure_designUnitMeasure (bernoulliDesign (ι := ι) p hp0.le hp1.le)
  obtain ⟨hind, hreal⟩ := indepFun_unitTreatment_bernoulli hp0.le hp1.le Wu Yu
  exact isConsistent_sampleNaiveContrast_of_indepFun Measurable.of_discrete Measurable.of_discrete
    (fun _ => Measurable.of_discrete) (fun _ => Integrable.of_finite) hind
    (by rw [hreal]; exact hp0) (by rw [hreal]; exact hp1) hO hlaw

/-- **The difference in arm means under a completely randomized superpopulation is
consistent**, when `0 < n₁ < N`. -/
theorem isConsistent_sampleNaiveContrast_complete [Nonempty ι] {Ξ : Type*}
    {mΞ : MeasurableSpace Ξ} {P : Measure Ξ} [IsProbabilityMeasure P] {n₁ : ℕ}
    (h : n₁ ≤ Fintype.card ι) (h0 : 0 < n₁) (h1 : n₁ < Fintype.card ι) (Wu : ι → 𝒲)
    (Yu : Bool → ι → ℝ) {O : ℕ → Ξ → 𝒲 × Bool × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (designUnitMeasure (completeDesign (ι := ι) n₁ h)).map fun x =>
      (Wu x.1, unitTreatment x, obsOutcome unitTreatment (fun b x => Yu b x.1) x)) :
    IsConsistent (sampleNaiveContrast O)
      (ate (designUnitMeasure (completeDesign (ι := ι) n₁ h)) fun b x => Yu b x.1) P := by
  have := isProbabilityMeasure_designUnitMeasure (completeDesign (ι := ι) n₁ h)
  obtain ⟨hind, hreal⟩ := indepFun_unitTreatment_complete h Wu Yu
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hp0 : 0 < (designUnitMeasure (completeDesign (ι := ι) n₁ h)).real
      (unitTreatment ⁻¹' {true}) := by
    rw [hreal]; exact div_pos (Nat.cast_pos.2 h0) hN
  have hp1 : (designUnitMeasure (completeDesign (ι := ι) n₁ h)).real
      (unitTreatment ⁻¹' {true}) < 1 := by
    rw [hreal, div_lt_one hN]; exact Nat.cast_lt.2 h1
  exact isConsistent_sampleNaiveContrast_of_indepFun Measurable.of_discrete Measurable.of_discrete
    (fun _ => Measurable.of_discrete) (fun _ => Integrable.of_finite) hind hp0 hp1 hO hlaw

end PointTreatment

end CausalInference
