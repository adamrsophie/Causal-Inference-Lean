/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.Counterexamples

/-!
# Instrumental variables under heterogeneous treatment effects

What the Wald ratio of a binary instrument identifies when unit-level treatment effects vary,
following NICE Decision Support Unit Technical Support Document 17 (Faria, Hernandez Alava,
Manca and Wailoo, 2015, *The use of observational data to inform estimates of treatment
effectiveness in technology appraisal: methods for comparative individual patient data*),
Section 2.1.2 (types of treatment effects), Section 2.4.1 (instrumental variable methods) and
Question 17 (overidentifying restrictions) of its checklist. The document states these facts in
words; the statements below are their formalization.

The probability setting is that of `CausalInference.IVModel`: a general probability space, a
binary instrument, a binary treatment and real potential outcomes, with conditional means taken
against conditional measures. The concrete models are finite product measures.

## Main definitions

* `CausalInference.IVModel.att`: the average treatment effect on the treated
  `E[Y z 1 - Y z 0 | Dobs = true]`.
* `IVModel.NoSelectionOnGains`: the unit-level effect is integrable and mean independent of the
  principal stratum (in unnormalized form, so that null strata impose nothing).

## Main results

* `IVModel.wald_eq_of_setIntegral_eq`: without monotonicity, if compliers and defiers have the
  same mean effect `τ`, the Wald ratio is `τ`.
* `IVModel.wald_eq_ate_of_noSelectionOnGains`: under exclusion, independence, relevance and
  integrability (no monotonicity), no selection on gains makes the Wald ratio the average
  treatment effect (under a probability measure); `IVModel.noSelectionOnGains_iff` gives the
  conditional form of the hypothesis.
* `IVModel.wald_eq_of_homogeneous`: with a constant effect `β` the Wald ratio is `β`, defiers
  allowed; `IVModel.homogeneous_collapse`: then the average effect, the effect on the treated,
  the complier effect and the Wald ratio all equal `β` when the compliers have positive mass
  (positive mass of the treated follows from relevance,
  `IVModel.Relevance.measure_dobs_true_ne_zero`).
* `IVModel.wald_eq_wald_of_homogeneous`: overidentification under a constant effect: two valid
  instruments give the same Wald ratio.
* `IVHeterogeneity.roy_separation`: a Roy model (units select treatment when their gain exceeds
  an instrument-dependent cost) satisfying all the LATE assumptions, in which the average
  effect (`8 / 3`), the effect on the treated (`14 / 3`) and the complier effect (`2`, the Wald
  ratio) are pairwise distinct; there no selection on gains fails and the Wald ratio is not the
  average effect.
* `IVHeterogeneity.twoInstruments_wald_ne`: one population with two valid instruments, sharing
  potential outcomes and observed treatment and outcome, whose complier sets differ and whose
  Wald ratios are `1` and `3`.

The covariance-ratio form of the constant-effect result and the linear model version of
overidentification are in `CausalInference.InstrumentalVariables.InvalidInstrument`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

namespace IVModel

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- The average treatment effect on the treated `E[Y z true - Y z false | Dobs = true]` at
instrument value `z`: the mean unit-level effect under the conditional measure given that the
observed treatment is `true`. -/
noncomputable def att (μ : Measure Ω) (z : Bool) : ℝ :=
  ∫ ω, M.effect z ω ∂μ[|{ω | M.Dobs ω = true}]

/-- **The Wald ratio without monotonicity.** Assume the exclusion restriction, instrument
independence, relevance and integrable responses `Y z (D z)`, but not monotonicity. If the
compliers and the defiers have the same mean effect `τ`, in the unnormalized form
`∫_compliers (Y z 1 - Y z 0) = τ P(compliers)` and `∫_defiers (Y z 1 - Y z 0) = τ P(defiers)`
(which for a stratum of positive mass says that its mean effect is `τ`, and for a null stratum
is automatic), then the Wald ratio equals `τ`. -/
theorem wald_eq_of_setIntegral_eq [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hR : M.Relevance μ) (hY : ∀ z, Integrable (M.YD z) μ)
    {z : Bool} {τ : ℝ}
    (hC : ∫ ω in M.compliers, M.effect z ω ∂μ = τ * μ.real M.compliers)
    (hD : ∫ ω in M.defiers, M.effect z ω ∂μ = τ * μ.real M.defiers) :
    M.wald μ = τ := by
  rw [wald, div_eq_iff hR.2.2, M.reducedForm_eq hE hI hY hR.1 hR.2.1 z, hC, hD,
    M.firstStage_eq hI hR.1 hR.2.1]
  ring

/-! ### No selection on gains -/

/-- **No selection on gains** at instrument value `z`: the unit-level effect `Y z 1 - Y z 0` is
integrable and mean independent of the principal stratum, in the unnormalized form
`∫_s (Y z 1 - Y z 0) = P(s) E[Y z 1 - Y z 0]` for each of the four strata `s`. Integrability is
part of the condition, so that it cannot hold through integrals that are `0` by the convention
for non-integrable functions. Under a probability measure `μ`, `IVModel.ate` is the population
mean effect and, for a stratum of positive mass, the condition says
`E[Y z 1 - Y z 0 | s] = E[Y z 1 - Y z 0]` (`IVModel.noSelectionOnGains_iff`); for a null stratum
it is automatic. -/
def NoSelectionOnGains (μ : Measure Ω) (z : Bool) : Prop :=
  Integrable (M.effect z) μ ∧
    ∀ s, ∫ ω in M.stratum s, M.effect z ω ∂μ = μ.real (M.stratum s) * M.ate μ z

/-- Under a probability measure, no selection on gains is equivalent to the conditional form:
the effect is integrable and every principal stratum of positive mass has mean effect equal to
the average treatment effect. -/
theorem noSelectionOnGains_iff [IsProbabilityMeasure μ] {z : Bool} :
    M.NoSelectionOnGains μ z ↔ Integrable (M.effect z) μ ∧
      ∀ s, μ (M.stratum s) ≠ 0 → ∫ ω, M.effect z ω ∂μ[|M.stratum s] = M.ate μ z := by
  refine and_congr_right' (forall_congr' fun s ↦ ?_)
  rw [integral_cond_eq_inv_mul]
  by_cases h0 : μ (M.stratum s) = 0
  · simp [h0, setIntegral_measure_zero _ h0, measureReal_def]
  · have hr : μ.real (M.stratum s) ≠ 0 := by
      rw [measureReal_def]
      exact ENNReal.toReal_ne_zero.2 ⟨h0, measure_ne_top _ _⟩
    simp only [h0, ne_eq, not_false_eq_true, forall_const]
    constructor
    · intro h; rw [h, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
    · intro h; rw [← h, ← mul_assoc, mul_inv_cancel₀ hr, one_mul]

/-- **The Wald ratio is the average treatment effect without selection on gains** (NICE DSU
TSD 17, Section 2.4.1: with heterogeneous effects, IV recovers the average treatment effect when
selection into treatment is not influenced by the individual gain). Assume the exclusion
restriction, instrument independence, relevance and integrable potential outcomes, but not
monotonicity. If the unit-level effect is mean independent of the principal stratum
(`IVModel.NoSelectionOnGains`), the Wald ratio equals `IVModel.ate`, which under a probability
measure is the average treatment effect `E[Y z 1 - Y z 0]`. Only the complier and defier
strata are used. -/
theorem wald_eq_ate_of_noSelectionOnGains [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hR : M.Relevance μ) (hY : ∀ z d, Integrable (M.Y z d) μ)
    {z : Bool} (hN : M.NoSelectionOnGains μ z) :
    M.wald μ = M.ate μ z :=
  M.wald_eq_of_setIntegral_eq hE hI hR (fun z ↦ M.integrable_Y_D (hY z) z)
    ((hN.2 .complier).trans (mul_comm _ _)) ((hN.2 .defier).trans (mul_comm _ _))

/-! ### Homogeneous effects -/

/-- Under a homogeneous effect `Y z 1 - Y z 0 = β` almost surely, the integral of the effect
over any set `s` is `β P(s)`. -/
theorem setIntegral_effect_of_homogeneous {z : Bool} {β : ℝ}
    (hβ : ∀ᵐ ω ∂μ, M.effect z ω = β) (s : Set Ω) :
    ∫ ω in s, M.effect z ω ∂μ = β * μ.real s := by
  rw [integral_congr_ae (ae_restrict_of_ae hβ), setIntegral_const, smul_eq_mul, mul_comm]

/-- Under a homogeneous effect `β`, the average treatment effect is `β`. -/
theorem ate_eq_of_homogeneous [IsProbabilityMeasure μ] {z : Bool} {β : ℝ}
    (hβ : ∀ᵐ ω ∂μ, M.effect z ω = β) : M.ate μ z = β := by
  rw [ate, integral_congr_ae hβ, integral_const, probReal_univ, one_smul]

/-- Under a homogeneous effect `β`, the mean effect given any event `s` of positive mass is
`β`. -/
theorem integral_cond_effect_of_homogeneous {z : Bool} {β : ℝ}
    (hβ : ∀ᵐ ω ∂μ, M.effect z ω = β) {s : Set Ω} (hs : μ s ≠ 0) (hs' : μ s ≠ ⊤) :
    ∫ ω, M.effect z ω ∂μ[|s] = β := by
  have := cond_isProbabilityMeasure_of_finite hs hs'
  rw [integral_congr_ae (cond_absolutelyContinuous.ae_le hβ), integral_const, probReal_univ,
    one_smul]

/-- Under a homogeneous effect `β` and `P(compliers) ≠ 0`, the complier average causal effect
is `β`. -/
theorem complierEffect_eq_of_homogeneous [IsFiniteMeasure μ] {z : Bool} {β : ℝ}
    (hβ : ∀ᵐ ω ∂μ, M.effect z ω = β) (hC : μ M.compliers ≠ 0) : M.complierEffect μ z = β :=
  M.integral_cond_effect_of_homogeneous hβ hC (measure_ne_top _ _)

/-- Under a homogeneous effect `β` and `P(Dobs = true) ≠ 0`, the average treatment effect on
the treated is `β`. -/
theorem att_eq_of_homogeneous [IsFiniteMeasure μ] {z : Bool} {β : ℝ}
    (hβ : ∀ᵐ ω ∂μ, M.effect z ω = β) (hT : μ {ω | M.Dobs ω = true} ≠ 0) : M.att μ z = β :=
  M.integral_cond_effect_of_homogeneous hβ hT (measure_ne_top _ _)

/-- **The Wald ratio under a homogeneous effect, without monotonicity.** Under the exclusion
restriction, instrument independence, relevance and integrable responses `Y z (D z)`, if the
unit-level effect equals a constant `β` almost surely, the Wald ratio equals `β`. Defiers are
allowed: the first stage is `P(compliers) - P(defiers)` and the reduced form is `β` times it. -/
theorem wald_eq_of_homogeneous [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hR : M.Relevance μ) (hY : ∀ z, Integrable (M.YD z) μ)
    {z : Bool} {β : ℝ} (hβ : ∀ᵐ ω ∂μ, M.effect z ω = β) : M.wald μ = β :=
  M.wald_eq_of_setIntegral_eq hE hI hR hY (M.setIntegral_effect_of_homogeneous hβ _)
    (M.setIntegral_effect_of_homogeneous hβ _)

/-- Relevance forces the treated to have positive mass: if `P(Dobs = true) = 0`, then
`Dobs` is coded `0` almost surely, also under each conditional measure given the instrument
(which is absolutely continuous with respect to `μ`), so the first stage is `0`. -/
theorem Relevance.measure_dobs_true_ne_zero {M : IVModel Ω} (hR : M.Relevance μ) :
    μ {ω | M.Dobs ω = true} ≠ 0 := by
  intro h0
  have hae : M.DobsReal =ᵐ[μ] fun _ ↦ 0 :=
    (measure_eq_zero_iff_ae_notMem.1 h0).mono fun ω hω ↦ by
      simp only [Set.mem_ofPred_eq, Bool.not_eq_true] at hω
      simp [DobsReal, boolToReal, hω]
  have hz : ∀ z, M.condMean μ M.DobsReal z = 0 := fun z ↦ by
    rw [condMean, integral_congr_ae (cond_absolutelyContinuous.ae_le hae), integral_zero]
  exact hR.2.2 (by rw [firstStage, hz, hz, sub_zero])

/-- **Homogeneity collapses the treatment effect parameters** (NICE DSU TSD 17, Section 2.1.2:
"a treatment effect is homogeneous if ... It follows in this case that the ATE, ATT and LATE are
identical"). Under the exclusion restriction, instrument independence, relevance and integrable
responses `Y z (D z)`, if the unit-level effect equals `β` almost surely and the compliers have
positive mass, then the average treatment effect, the effect on the treated, the complier
average causal effect and the Wald ratio all equal `β`. Positive mass of the treated follows
from relevance (`IVModel.Relevance.measure_dobs_true_ne_zero`). Positive mass of the compliers
does not: without monotonicity the first stage can be carried by defiers alone, so it is a
hypothesis. -/
theorem homogeneous_collapse [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hR : M.Relevance μ) (hY : ∀ z, Integrable (M.YD z) μ)
    {z : Bool} {β : ℝ} (hβ : ∀ᵐ ω ∂μ, M.effect z ω = β) (hC : μ M.compliers ≠ 0) :
    M.ate μ z = β ∧ M.att μ z = β ∧ M.complierEffect μ z = β ∧ M.wald μ = β :=
  ⟨M.ate_eq_of_homogeneous hβ, M.att_eq_of_homogeneous hβ hR.measure_dobs_true_ne_zero,
    M.complierEffect_eq_of_homogeneous hβ hC, M.wald_eq_of_homogeneous hE hI hR hY hβ⟩

/-- A homogeneous effect satisfies no selection on gains. -/
theorem noSelectionOnGains_of_homogeneous [IsProbabilityMeasure μ] {z : Bool} {β : ℝ}
    (hβ : ∀ᵐ ω ∂μ, M.effect z ω = β) : M.NoSelectionOnGains μ z :=
  ⟨(integrable_const β).congr (hβ.mono fun _ h ↦ h.symm), fun s ↦ by
    rw [M.setIntegral_effect_of_homogeneous hβ, M.ate_eq_of_homogeneous hβ, mul_comm]⟩

/-- **Overidentification under a constant effect** (NICE DSU TSD 17, Question 17). Two binary
instrumental variable models on the same probability space, each satisfying the exclusion
restriction, instrument independence, relevance and integrability, whose unit-level effects
both equal the same constant `β` almost surely, have the same Wald ratio `β`. Under heterogeneous
effects two valid instruments can have different Wald ratios
(`IVHeterogeneity.twoInstruments_wald_ne`), so a rejected overidentification test does not by
itself show that an instrument is invalid. -/
theorem wald_eq_wald_of_homogeneous [IsFiniteMeasure μ] {M₁ M₂ : IVModel Ω}
    (hE₁ : M₁.Exclusion μ) (hI₁ : M₁.InstrumentIndependence μ) (hR₁ : M₁.Relevance μ)
    (hY₁ : ∀ z, Integrable (M₁.YD z) μ) (hE₂ : M₂.Exclusion μ)
    (hI₂ : M₂.InstrumentIndependence μ) (hR₂ : M₂.Relevance μ)
    (hY₂ : ∀ z, Integrable (M₂.YD z) μ) {z₁ z₂ : Bool} {β : ℝ}
    (hβ₁ : ∀ᵐ ω ∂μ, M₁.effect z₁ ω = β) (hβ₂ : ∀ᵐ ω ∂μ, M₂.effect z₂ ω = β) :
    M₁.wald μ = M₂.wald μ := by
  rw [M₁.wald_eq_of_homogeneous hE₁ hI₁ hR₁ hY₁ hβ₁, M₂.wald_eq_of_homogeneous hE₂ hI₂ hR₂ hY₂ hβ₂]

end IVModel

namespace IVHeterogeneity

open IVCounterexample IVModel

variable {n : ℕ}

/-- The mean of any function on the finite product model `IVCounterexample.P n` is its average
over the `2 n` points. -/
theorem integral_P [NeZero n] (f : Space n → ℝ) :
    ∫ ω, f ω ∂P n = (∑ u, (f (true, u) + f (false, u))) / (2 * n) := by
  rw [integral_fintype .of_finite]
  have hs : ∀ ω : Space n, (P n).real {ω} = ((2 : ℝ) * n)⁻¹ := by
    intro ω
    rw [measureReal_def, P, ← Set.singleton_prod_singleton, Measure.prod_prod, uniformOn_univ,
      uniformOn_univ]
    simp [ENNReal.toReal_mul, mul_comm]
  simp only [hs, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.mul_sum,
    ← Finset.sum_add_distrib]
  ring

/-- In the finite product model every set containing a point has positive mass. -/
theorem P_ne_zero_of_mem {s : Set (Space n)} {ω : Space n} (hω : ω ∈ s) : P n s ≠ 0 :=
  fun h ↦ measure_singleton_ne_zero ω (measure_mono_null (Set.singleton_subset_iff.2 hω) h)

/-! ### A Roy model: selection on gains separates the parameters -/

/-- The individual gains `Y 1 - Y 0` of the three unit types of the Roy model: `0`, `2`, `6`. -/
def royGain : Fin 3 → ℝ := ![0, 2, 6]

/-- The cost of treatment in the Roy model, shifted by the instrument: `1` when the instrument is
`true` and `4` when it is `false`. -/
def royCost (z : Bool) : ℝ := if z then 1 else 4

/-- A Roy model on `Bool × Fin 3` (the instrument is a fair coin, independent of a uniform unit
type): a unit takes the treatment exactly when its gain exceeds the cost set by the instrument
(`IVHeterogeneity.roy_D_eq`). Type `0` (gain `0`) is a never-taker, type `1` (gain `2`) a
complier, type `2` (gain `6`) an always-taker. The outcome is the gain if treated and `0`
otherwise, whatever the instrument value. -/
def roy : IVModel (Space 3) where
  Z := Prod.fst
  D z ω := if ω.2 = 0 then false else if ω.2 = 1 then z else true
  Y _ d ω := if d then royGain ω.2 else 0
  measurable_Z := measurable_fst
  measurable_D _ := measurable_of_countable _
  measurable_Y _ _ := measurable_of_countable _

/-- Selection on gains: in `roy`, a unit is treated under instrument value `z` exactly when its
gain exceeds the cost `royCost z`. -/
theorem roy_D_eq (z : Bool) (ω : Space 3) :
    roy.D z ω = decide (royCost z < royGain ω.2) := by
  obtain ⟨b, u⟩ := ω
  fin_cases u <;> cases z <;> norm_num [roy, royCost, royGain]

theorem roy_compliers : roy.compliers = {ω | ω.2 = 1} := by
  ext ⟨b, u⟩
  fin_cases u <;> simp [mem_compliers, roy]

theorem roy_independence : roy.InstrumentIndependence (P 3) :=
  indepFun_fst fun u ↦ roy.potentials (true, u)

theorem roy_monotonicity : roy.Monotonicity (P 3) :=
  Filter.Eventually.of_forall fun ⟨b, u⟩ ↦ by fin_cases u <;> simp [roy]

/-- `roy` satisfies all the hypotheses of the LATE theorem. -/
theorem roy_assumptions : roy.LATEAssumptions (P 3) where
  exclusion _ := Filter.EventuallyEq.rfl
  independence := roy_independence
  monotonicity := roy_monotonicity
  relevance := by
    have h₁ : P 3 (roy.instrumentEq true) ≠ 0 :=
      P_ne_zero_of_mem (ω := ((true, 0) : Space 3)) rfl
    have h₀ : P 3 (roy.instrumentEq false) ≠ 0 :=
      P_ne_zero_of_mem (ω := ((false, 0) : Space 3)) rfl
    refine (relevance_iff roy roy_independence roy_monotonicity h₁ h₀).2 ?_
    rw [measureReal_def]
    exact ENNReal.toReal_pos (P_ne_zero_of_mem (ω := ((true, 1) : Space 3))
      (by simp [roy_compliers])) (measure_ne_top _ _)
  integrable _ := .of_finite

theorem roy_complierEffect (z : Bool) : roy.complierEffect (P 3) z = 2 := by
  have hC : P 3 roy.compliers ≠ 0 :=
    P_ne_zero_of_mem (ω := ((true, 1) : Space 3)) (by simp [roy_compliers])
  have := cond_isProbabilityMeasure (μ := P 3) hC
  rw [IVModel.complierEffect]
  refine (integral_congr_ae (g := fun _ ↦ (2 : ℝ)) ?_).trans (by simp)
  refine ((ae_cond_mem roy.measurableSet_compliers).mono fun ω hω ↦ ?_)
  rw [roy_compliers] at hω
  simp only [Set.mem_ofPred_eq] at hω
  simp [IVModel.effect, roy, royGain, hω]

theorem roy_wald : roy.wald (P 3) = 2 := by
  rw [roy_assumptions.wald_eq true, roy_complierEffect]

theorem roy_ate (z : Bool) : roy.ate (P 3) z = 8 / 3 := by
  rw [IVModel.ate, integral_of_snd _ fun _ ↦ rfl]
  simp [Fin.sum_univ_three, roy, royGain, IVModel.effect]
  norm_num

theorem roy_att (z : Bool) : roy.att (P 3) z = 14 / 3 := by
  set S : Set (Space 3) := {ω | roy.Dobs ω = true}
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  rw [IVModel.att, integral_cond_eq_inv_mul, ← integral_indicator hS,
    ← integral_indicator_one hS, integral_P, integral_P]
  simp [S, Set.indicator, Fin.sum_univ_three, roy, royGain, IVModel.effect, IVModel.Dobs]
  norm_num

/-- **Heterogeneity with selection on gains separates the parameters** (NICE DSU TSD 17,
Section 2.1.2: "selection into treatment will depend on the determinants of this heterogeneity
and this may lead to differences between the treatment parameters, ATE, ATT and LATE"). In the
Roy model `roy`, all the hypotheses of the LATE theorem hold; the average treatment effect is
`8 / 3`, the effect on the treated is `14 / 3`, and the complier average causal effect, equal to
the Wald ratio, is `2`: the three parameters are pairwise distinct. No selection on gains fails,
and the Wald ratio differs from the average treatment effect, so that hypothesis of
`IVModel.wald_eq_ate_of_noSelectionOnGains` cannot be dropped. -/
theorem roy_separation :
    roy.LATEAssumptions (P 3) ∧ roy.ate (P 3) true = 8 / 3 ∧ roy.att (P 3) true = 14 / 3 ∧
      roy.complierEffect (P 3) true = 2 ∧ roy.wald (P 3) = 2 ∧
      roy.ate (P 3) true ≠ roy.att (P 3) true ∧
      roy.ate (P 3) true ≠ roy.complierEffect (P 3) true ∧
      roy.att (P 3) true ≠ roy.complierEffect (P 3) true ∧
      ¬ roy.NoSelectionOnGains (P 3) true ∧ roy.wald (P 3) ≠ roy.ate (P 3) true := by
  have hne : roy.wald (P 3) ≠ roy.ate (P 3) true := by
    rw [roy_wald, roy_ate]; norm_num
  refine ⟨roy_assumptions, roy_ate true, roy_att true, roy_complierEffect true, roy_wald,
    by rw [roy_ate, roy_att]; norm_num, by rw [roy_ate, roy_complierEffect]; norm_num,
    by rw [roy_att, roy_complierEffect]; norm_num, fun hN ↦ hne ?_, hne⟩
  exact roy.wald_eq_ate_of_noSelectionOnGains roy_assumptions.exclusion
    roy_assumptions.independence roy_assumptions.relevance (fun _ _ ↦ .of_finite) hN

/-! ### Two valid instruments with different local effects -/

/-- The sample space of the two-instrument model: the first instrument, the second instrument,
and a unit type in `Fin 2`. -/
abbrev Space2 : Type := Bool × Bool × Fin 2

/-- Two independent fair coins (the two instruments) and an independent uniform unit type. -/
noncomputable def P2 : Measure Space2 :=
  (uniformOn (Set.univ : Set Bool)).prod
    ((uniformOn (Set.univ : Set Bool)).prod (uniformOn (Set.univ : Set (Fin 2))))

instance : IsProbabilityMeasure P2 := by unfold P2; infer_instance

theorem P2_singleton (ω : Space2) : P2 {ω} = 2⁻¹ * (2⁻¹ * 2⁻¹) := by
  obtain ⟨a, b, u⟩ := ω
  rw [P2, ← Set.singleton_prod_singleton, Measure.prod_prod, ← Set.singleton_prod_singleton,
    Measure.prod_prod, uniformOn_univ, uniformOn_univ, uniformOn_univ]
  simp

theorem P2_ne_zero_of_mem {s : Set Space2} {ω : Space2} (hω : ω ∈ s) : P2 s ≠ 0 := by
  refine fun h ↦ ?_
  have h0 := measure_mono_null (Set.singleton_subset_iff.2 hω) h
  rw [P2_singleton] at h0
  simp at h0

/-- The exchange of the two instruments, `(a, b, u) ↦ (b, a, u)`. -/
def swapInstruments (ω : Space2) : Space2 := (ω.2.1, (ω.1, ω.2.2))

theorem map_swapInstruments : P2.map swapInstruments = P2 := by
  refine Measure.ext_of_singleton fun ω ↦ ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have h : swapInstruments ⁻¹' {ω} = {swapInstruments ω} := by
    ext ⟨a, b, u⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, swapInstruments, Prod.ext_iff]
    tauto
  rw [h, P2_singleton, P2_singleton]

/-- The first instrument is independent of every function of the second instrument and the unit
type. -/
theorem indepFun_first {β : Type*} [MeasurableSpace β] (h : Bool × Fin 2 → β) :
    IndepFun Prod.fst (fun ω : Space2 ↦ h ω.2) P2 :=
  indepFun_prod (X := id) measurable_id (measurable_of_countable h)

/-- The second instrument is independent of every function of the first instrument and the unit
type. -/
theorem indepFun_second {β : Type*} [MeasurableSpace β] (h : Bool × Fin 2 → β) :
    IndepFun (fun ω : Space2 ↦ ω.2.1) (fun ω ↦ h (ω.1, ω.2.2)) P2 := by
  have key := indepFun_first h
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at key ⊢
  intro s t hs ht
  have e : ∀ A : Set Space2, P2 (swapInstruments ⁻¹' A) = P2 A := fun A ↦ by
    rw [← Measure.map_apply (measurable_of_countable _) (Set.to_countable A).measurableSet,
      map_swapInstruments]
  rw [show (fun ω : Space2 ↦ ω.2.1) ⁻¹' s ∩ (fun ω : Space2 ↦ h (ω.1, ω.2.2)) ⁻¹' t =
      swapInstruments ⁻¹' (Prod.fst ⁻¹' s ∩ (fun ω : Space2 ↦ h ω.2) ⁻¹' t) from rfl,
    show (fun ω : Space2 ↦ ω.2.1) ⁻¹' s = swapInstruments ⁻¹' (Prod.fst ⁻¹' s) from rfl,
    show (fun ω : Space2 ↦ h (ω.1, ω.2.2)) ⁻¹' t =
      swapInstruments ⁻¹' ((fun ω : Space2 ↦ h ω.2) ⁻¹' t) from rfl,
    e, e, e, key s t hs ht]

/-- The treatment rule of the two-instrument model: a unit of type `0` takes the treatment
exactly when the first instrument is `true`, a unit of type `1` exactly when the second is. -/
def treatmentRule (z₁ z₂ : Bool) (u : Fin 2) : Bool := if u = 0 then z₁ else z₂

/-- The individual gains of the two unit types: `1` and `3`. -/
def twoGain : Fin 2 → ℝ := ![1, 3]

/-- The two-instrument population seen through the first instrument: the potential treatment
under first-instrument value `z` is `treatmentRule z Z₂ u`, with the second instrument `Z₂` at
its realized value. The outcome is the gain if treated and `0` otherwise. -/
def firstIV : IVModel Space2 where
  Z := Prod.fst
  D z ω := treatmentRule z ω.2.1 ω.2.2
  Y _ d ω := if d then twoGain ω.2.2 else 0
  measurable_Z := measurable_fst
  measurable_D _ := measurable_of_countable _
  measurable_Y _ _ := measurable_of_countable _

/-- The same population seen through the second instrument: the potential treatment under
second-instrument value `z` is `treatmentRule Z₁ z u`, with the first instrument `Z₁` at its
realized value. -/
def secondIV : IVModel Space2 where
  Z ω := ω.2.1
  D z ω := treatmentRule ω.1 z ω.2.2
  Y _ d ω := if d then twoGain ω.2.2 else 0
  measurable_Z := measurable_of_countable _
  measurable_D _ := measurable_of_countable _
  measurable_Y _ _ := measurable_of_countable _

theorem firstIV_compliers : firstIV.compliers = {ω | ω.2.2 = 0} := by
  ext ⟨a, b, u⟩
  fin_cases u <;> cases b <;> simp [mem_compliers, firstIV, treatmentRule]

theorem secondIV_compliers : secondIV.compliers = {ω | ω.2.2 = 1} := by
  ext ⟨a, b, u⟩
  fin_cases u <;> cases a <;> simp [mem_compliers, secondIV, treatmentRule]

theorem firstIV_assumptions : firstIV.LATEAssumptions P2 := by
  have hI : firstIV.InstrumentIndependence P2 := indepFun_first fun v ↦ firstIV.potentials (true, v)
  have hM : firstIV.Monotonicity P2 :=
    Filter.Eventually.of_forall fun ⟨a, b, u⟩ ↦ by
      fin_cases u <;> cases b <;> simp [firstIV, treatmentRule]
  have h₁ : P2 (firstIV.instrumentEq true) ≠ 0 :=
    P2_ne_zero_of_mem (ω := ((true, true, 0) : Space2)) rfl
  have h₀ : P2 (firstIV.instrumentEq false) ≠ 0 :=
    P2_ne_zero_of_mem (ω := ((false, true, 0) : Space2)) rfl
  refine ⟨fun _ ↦ Filter.EventuallyEq.rfl, hI, hM, ?_, fun _ ↦ .of_finite⟩
  refine (relevance_iff firstIV hI hM h₁ h₀).2 ?_
  rw [measureReal_def]
  exact ENNReal.toReal_pos (P2_ne_zero_of_mem (ω := ((true, true, 0) : Space2))
    (by simp [firstIV_compliers])) (measure_ne_top _ _)

theorem secondIV_assumptions : secondIV.LATEAssumptions P2 := by
  have hI : secondIV.InstrumentIndependence P2 :=
    indepFun_second fun v ↦ secondIV.potentials (v.1, true, v.2)
  have hM : secondIV.Monotonicity P2 :=
    Filter.Eventually.of_forall fun ⟨a, b, u⟩ ↦ by
      fin_cases u <;> cases a <;> simp [secondIV, treatmentRule]
  have h₁ : P2 (secondIV.instrumentEq true) ≠ 0 :=
    P2_ne_zero_of_mem (ω := ((true, true, 0) : Space2)) rfl
  have h₀ : P2 (secondIV.instrumentEq false) ≠ 0 :=
    P2_ne_zero_of_mem (ω := ((true, false, 0) : Space2)) rfl
  refine ⟨fun _ ↦ Filter.EventuallyEq.rfl, hI, hM, ?_, fun _ ↦ .of_finite⟩
  refine (relevance_iff secondIV hI hM h₁ h₀).2 ?_
  rw [measureReal_def]
  exact ENNReal.toReal_pos (P2_ne_zero_of_mem (ω := ((true, true, 1) : Space2))
    (by simp [secondIV_compliers])) (measure_ne_top _ _)

theorem firstIV_wald : firstIV.wald P2 = 1 := by
  rw [firstIV_assumptions.wald_eq true, IVModel.complierEffect]
  have hC : P2 firstIV.compliers ≠ 0 :=
    P2_ne_zero_of_mem (ω := ((true, true, 0) : Space2)) (by simp [firstIV_compliers])
  have := cond_isProbabilityMeasure (μ := P2) hC
  refine (integral_congr_ae (g := fun _ ↦ (1 : ℝ)) ?_).trans (by simp)
  refine ((ae_cond_mem firstIV.measurableSet_compliers).mono fun ω hω ↦ ?_)
  rw [firstIV_compliers] at hω
  simp only [Set.mem_ofPred_eq] at hω
  simp [IVModel.effect, firstIV, twoGain, hω]

theorem secondIV_wald : secondIV.wald P2 = 3 := by
  rw [secondIV_assumptions.wald_eq true, IVModel.complierEffect]
  have hC : P2 secondIV.compliers ≠ 0 :=
    P2_ne_zero_of_mem (ω := ((true, true, 1) : Space2)) (by simp [secondIV_compliers])
  have := cond_isProbabilityMeasure (μ := P2) hC
  refine (integral_congr_ae (g := fun _ ↦ (3 : ℝ)) ?_).trans (by simp)
  refine ((ae_cond_mem secondIV.measurableSet_compliers).mono fun ω hω ↦ ?_)
  rw [secondIV_compliers] at hω
  simp only [Set.mem_ofPred_eq] at hω
  simp [IVModel.effect, secondIV, twoGain, hω]

/-- **The local effect depends on the instrument** (NICE DSU TSD 17, Section 2.4.1: "Clearly,
the LATE depends on the instrument. Therefore, different instruments will give different values
of the LATE if they induce different groups of people to engage in treatment"; and Question 17).
One population carries two instruments: `firstIV` and `secondIV` share the probability space,
the potential outcomes, the observed treatment and the observed outcome, and each satisfies all
the hypotheses of the LATE theorem (each instrument is independent of the other and of the unit
type). Their complier sets are disjoint and nonempty, and their Wald ratios are `1` and `3`. The
unit-level effect is not almost surely constant (otherwise the two Wald ratios would agree by
`IVModel.wald_eq_wald_of_homogeneous`). So two valid instruments can fail an
overidentification comparison when effects are heterogeneous. -/
theorem twoInstruments_wald_ne :
    firstIV.LATEAssumptions P2 ∧ secondIV.LATEAssumptions P2 ∧ firstIV.Y = secondIV.Y ∧
      firstIV.Dobs = secondIV.Dobs ∧ firstIV.Yobs = secondIV.Yobs ∧
      Disjoint firstIV.compliers secondIV.compliers ∧
      P2 firstIV.compliers ≠ 0 ∧ P2 secondIV.compliers ≠ 0 ∧
      firstIV.wald P2 = 1 ∧ secondIV.wald P2 = 3 ∧
      ¬ ∃ β : ℝ, ∀ᵐ ω ∂P2, firstIV.effect true ω = β := by
  refine ⟨firstIV_assumptions, secondIV_assumptions, rfl, rfl, rfl, ?_,
    P2_ne_zero_of_mem (ω := ((true, true, 0) : Space2)) (by simp [firstIV_compliers]),
    P2_ne_zero_of_mem (ω := ((true, true, 1) : Space2)) (by simp [secondIV_compliers]),
    firstIV_wald, secondIV_wald, ?_⟩
  · rw [firstIV_compliers, secondIV_compliers]
    exact Set.disjoint_left.2 fun ω h₁ h₂ ↦ by
      simp only [Set.mem_ofPred_eq] at h₁ h₂; rw [h₁] at h₂; exact absurd h₂ (by decide)
  · rintro ⟨β, hβ⟩
    have h := IVModel.wald_eq_wald_of_homogeneous firstIV_assumptions.exclusion
      firstIV_assumptions.independence firstIV_assumptions.relevance
      firstIV_assumptions.integrable secondIV_assumptions.exclusion
      secondIV_assumptions.independence secondIV_assumptions.relevance
      secondIV_assumptions.integrable hβ (z₂ := true) hβ
    rw [firstIV_wald, secondIV_wald] at h
    norm_num at h

end IVHeterogeneity

end CausalInference
