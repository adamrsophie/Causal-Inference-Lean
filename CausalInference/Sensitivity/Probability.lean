/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Binomial
public import CausalInference.Sensitivity.BiasFormulas
public import CausalInference.Sensitivity.Rosenbaum

/-!
# Probability space versions of the sensitivity formulas

The files `CausalInference.Sensitivity.Rosenbaum` and `CausalInference.Sensitivity.BiasFormulas`
are finite and algebraic. This file ties them to measures.

* `Rosenbaum.binomialTail_eq_binomial_real`: the finite binomial tail `binomialTail n r k` is
  the mass of `{j | k ≤ j}` under Mathlib's binomial distribution `ProbabilityTheory.binomial`.
* `BiasFormulas.integral_cond_eq_observedMean`: for a measurable binary treatment `A`, a
  measurable binary confounder `U`, and an integrable outcome `Y` on a finite measure space,
  the conditional mean of `Y` given `A = a` is `observedMean` of the cell means
  `E[Y | A = a, U = u]` and the prevalences `P(U = 1 | A = a)` (law of total expectation).
* `BiasFormulas.integral_eq_standardized`: with consistency, conditional mean exchangeability
  given `U`, and positivity of treatment in every `U` stratum of positive probability, the mean
  potential outcome `E[Y^a]` is the `U`-standardized cell mean.
* `BiasFormulas.standardizedEffect_eq_ate`: under the same assumptions the standardized effect of
  the cell means is the average treatment effect `E[Y^1] - E[Y^0]`.
* `BiasFormulas.crude_sub_ate_eq`: hence the bias of the crude contrast
  `E[Y | A = 1] - E[Y | A = 0]` for the average treatment effect is given by the general bias
  formula of VanderWeele and Arah.

Positivity is required only in strata of positive probability, and it cannot be dropped: if
`A = U` is a fair coin and `Y^a = a`, then consistency and exchangeability hold but the cells
`{A = 1, U = 0}` and `{A = 0, U = 1}` are null, their conditional means are the junk value `0`,
the standardized difference is `1 / 2`, and the average treatment effect is `1`.

## References

* T. J. VanderWeele and O. A. Arah, *Bias formulas for sensitivity analysis of unmeasured
  confounding for general outcomes, treatments, and confounders*, Epidemiology (2011).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman and Hall/CRC (2020),
  chapter 2 (standardization).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

namespace Rosenbaum

/-- The finite binomial tail is the tail of Mathlib's binomial distribution: for `r ∈ [0, 1]`,
`binomialTail n r k = Bin(n, r)({j | k ≤ j})`. -/
theorem binomialTail_eq_binomial_real (n : ℕ) (r : unitInterval) (k : ℕ) :
    binomialTail n (r : ℝ) k = (binomial n r).real (Set.Ici k) := by
  -- the binomial distribution has no mass above `n`
  have hnull : (binomial n r) {j | ¬ j ≤ n} = 0 :=
    ae_iff.1 (ae_le_of_hasLaw_binomial (n := n) (p := r) (HasLaw.id (μ := binomial n r)))
  have hdiff : (binomial n r).real (Set.Ici k \ Set.Iic n) = 0 := by
    rw [measureReal_eq_zero_iff]
    refine measure_mono_null (fun j hj => ?_) hnull
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Iic] at hj
    exact hj.2
  have hcap : Set.Ici k ∩ Set.Iic n = ↑(Finset.Icc k n) := by
    ext j
    simp
  rw [← measureReal_inter_add_sdiff (s := Set.Ici k) measurableSet_Iic, hdiff, add_zero, hcap,
    ← sum_measureReal_singleton]
  simp only [binomial_real_singleton]
  rw [binomialTail, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

end Rosenbaum

namespace BiasFormulas

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Conditional means given an event -/

/-- For a finite measure, the set integral over `s` is `μ(s)` times the conditional mean given
`s`. Both sides vanish when `μ s = 0`. -/
theorem setIntegral_eq_measureReal_mul_integral_cond {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Set Ω} (f : Ω → ℝ) : ∫ ω in s, f ω ∂μ = μ.real s * ∫ ω, f ω ∂μ[|s] := by
  by_cases hs : μ s = 0
  · simp [Measure.restrict_eq_zero.mpr hs, measureReal_def, hs]
  · have hr : μ.real s ≠ 0 := by
      rw [measureReal_def]
      exact ENNReal.toReal_ne_zero.mpr ⟨hs, measure_ne_top μ s⟩
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
      ← measureReal_def]
    field_simp

/-- Law of total expectation over a binary covariate: for a finite measure, a measurable event
`s`, a measurable `X : Ω → Bool`, and an integrable `f`,
`μ(s) E[f | s] = ∑ₓ μ(s ∩ {X = x}) E[f | s ∩ {X = x}]`. -/
theorem measureReal_mul_integral_cond_eq_sum {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) {X : Ω → Bool} (hX : Measurable X) {f : Ω → ℝ}
    (hf : Integrable f μ) :
    μ.real s * ∫ ω, f ω ∂μ[|s] = ∑ x, μ.real (s ∩ X ⁻¹' {x}) *
      ∫ ω, f ω ∂μ[|s ∩ X ⁻¹' {x}] := by
  have hcells : ∀ x, MeasurableSet (s ∩ X ⁻¹' {x}) := fun x => hs.inter (hX (.singleton x))
  have hunion : (⋃ x, s ∩ X ⁻¹' {x}) = s := by ext ω; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun x => s ∩ X ⁻¹' {x}) := by
    intro x y hxy
    refine Set.disjoint_left.mpr fun ω hx hy => hxy ?_
    exact hx.2.symm.trans hy.2
  have htot : ∫ ω in s, f ω ∂μ = ∑ x, ∫ ω in s ∩ X ⁻¹' {x}, f ω ∂μ := by
    conv_lhs => rw [← hunion]
    exact integral_iUnion_fintype hcells hdisj fun x => hf.integrableOn
  rw [← setIntegral_eq_measureReal_mul_integral_cond, htot]
  simp_rw [setIntegral_eq_measureReal_mul_integral_cond (μ := μ) f]

/-- The real conditional probability: `P(t | s) = μ(s ∩ t) / μ(s)` for measurable `s`. -/
theorem cond_real_eq {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) (t : Set Ω) :
    (μ[|s]).real t = μ.real (s ∩ t) / μ.real s := by
  rw [measureReal_def, cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def,
    measureReal_def, div_eq_inv_mul]

/-! ### The probability space model -/

/-- The cell mean `E[Y | A = a, U = u]` of the outcome `Y` for a binary treatment `A` and a
binary confounder `U`. On a null cell this is the junk value `0`. -/
noncomputable def cellMean (μ : Measure Ω) (A U : Ω → Bool) (Y : Ω → ℝ) (a u : Bool) : ℝ :=
  ∫ ω, Y ω ∂μ[|A ⁻¹' {a} ∩ U ⁻¹' {u}]

/-- The prevalence `P(U = 1 | A = a)` of the confounder in treatment arm `a`. -/
noncomputable def condPrev (μ : Measure Ω) (A U : Ω → Bool) (a : Bool) : ℝ :=
  (μ[|A ⁻¹' {a}]).real (U ⁻¹' {true})

/-- The marginal prevalence `P(U = 1)` of the confounder. -/
noncomputable def margPrev (μ : Measure Ω) (U : Ω → Bool) : ℝ := μ.real (U ⁻¹' {true})

/-- The two levels of a binary variable split an event: for a finite measure,
`μ(s ∩ {U = 0}) = μ(s) - μ(s ∩ {U = 1})`. -/
theorem measureReal_inter_false {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} {U : Ω → Bool}
    (hU : Measurable U) :
    μ.real (s ∩ U ⁻¹' {false}) = μ.real s - μ.real (s ∩ U ⁻¹' {true}) := by
  have h := measureReal_inter_add_sdiff (μ := μ) (s := s) (hU (.singleton true))
  have hc : s \ U ⁻¹' {true} = s ∩ U ⁻¹' {false} := by
    ext ω
    simp
  rw [hc] at h
  linarith

/-- Law of total expectation for the observed mean: for a finite measure, measurable binary `A`
and `U`, an integrable outcome `Y`, and an arm `a` of positive measure,
`E[Y | A = a] = observedMean (cellMean μ A U Y) (condPrev μ A U) a`, that is,
`P(U = 1 | A = a) E[Y | A = a, U = 1] + P(U = 0 | A = a) E[Y | A = a, U = 0]`. -/
theorem integral_cond_eq_observedMean {μ : Measure Ω} [IsFiniteMeasure μ] {A U : Ω → Bool}
    (hA : Measurable A) (hU : Measurable U) {Y : Ω → ℝ} (hY : Integrable Y μ) (a : Bool)
    (ha : μ (A ⁻¹' {a}) ≠ 0) :
    ∫ ω, Y ω ∂μ[|A ⁻¹' {a}] = observedMean (cellMean μ A U Y) (condPrev μ A U) a := by
  have hs : MeasurableSet (A ⁻¹' {a}) := hA (.singleton a)
  have hr : μ.real (A ⁻¹' {a}) ≠ 0 := fun h =>
    ha ((measureReal_eq_zero_iff (measure_ne_top μ _)).1 h)
  have key := measureReal_mul_integral_cond_eq_sum hs hU hY
  rw [Fintype.sum_bool, measureReal_inter_false hU] at key
  unfold observedMean condPrev cellMean
  rw [cond_real_eq hs]
  apply mul_left_cancel₀ hr
  rw [key]
  field_simp

/-- Under the null of no treatment effect within levels of `U`, stated on the cell means
(`E[Y | A = a, U = u] = R u` for both arms), the observed mean in arm `a` is
`observedRisk R (condPrev μ A U) a`. With `Y` the indicator of an event, these are risks. -/
theorem integral_cond_eq_observedRisk {μ : Measure Ω} [IsFiniteMeasure μ] {A U : Ω → Bool}
    (hA : Measurable A) (hU : Measurable U) {Y : Ω → ℝ} (hY : Integrable Y μ) {R : Bool → ℝ}
    (hnull : ∀ a u, cellMean μ A U Y a u = R u) (a : Bool) (ha : μ (A ⁻¹' {a}) ≠ 0) :
    ∫ ω, Y ω ∂μ[|A ⁻¹' {a}] = observedRisk R (condPrev μ A U) a := by
  rw [integral_cond_eq_observedMean hA hU hY a ha]
  simp only [observedMean, observedRisk, hnull]

/-- Standardization identifies the mean potential outcome. Let `μ` be a probability measure,
`A U : Ω → Bool` measurable, `Y` the observed outcome and `Ypo a` the potential outcome under
treatment `a`, integrable. Assume consistency (`Y = Ypo A` almost surely), conditional mean
exchangeability given `U` in every cell of positive measure
(`E[Y^a | A = a, U = u] = E[Y^a | U = u]`), and positivity in every stratum of positive measure
(`P(U = u) > 0` implies `P(A = a, U = u) > 0`). Then `E[Y^a]` is the standardized mean
`standardizedMean (cellMean μ A U Y) (margPrev μ U) a`. -/
theorem integral_eq_standardized {μ : Measure Ω} [IsProbabilityMeasure μ] {A U : Ω → Bool}
    (hA : Measurable A) (hU : Measurable U) {Y : Ω → ℝ} {Ypo : Bool → Ω → ℝ}
    (hYpo : ∀ a, Integrable (Ypo a) μ) (hcons : ∀ᵐ ω ∂μ, Y ω = Ypo (A ω) ω)
    (hexch : ∀ a u, μ (A ⁻¹' {a} ∩ U ⁻¹' {u}) ≠ 0 →
      ∫ ω, Ypo a ω ∂μ[|A ⁻¹' {a} ∩ U ⁻¹' {u}] = ∫ ω, Ypo a ω ∂μ[|U ⁻¹' {u}])
    (hpos : ∀ a u, μ (U ⁻¹' {u}) ≠ 0 → μ (A ⁻¹' {a} ∩ U ⁻¹' {u}) ≠ 0) (a : Bool) :
    ∫ ω, Ypo a ω ∂μ = standardizedMean (cellMean μ A U Y) (margPrev μ U) a := by
  have hterm : ∀ u, μ.real (U ⁻¹' {u}) * ∫ ω, Ypo a ω ∂μ[|U ⁻¹' {u}] =
      μ.real (U ⁻¹' {u}) * cellMean μ A U Y a u := by
    intro u
    by_cases hu : μ (U ⁻¹' {u}) = 0
    · simp [measureReal_def, hu]
    · have hc := hpos a u hu
      have hcell : MeasurableSet (A ⁻¹' {a} ∩ U ⁻¹' {u}) :=
        (hA (.singleton a)).inter (hU (.singleton u))
      rw [← hexch a u hc, cellMean]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [ae_cond_mem hcell, cond_absolutelyContinuous.ae_le hcons] with ω hω h
      have hAω : A ω = a := hω.1
      rw [h, hAω]
  have key := measureReal_mul_integral_cond_eq_sum (μ := μ) MeasurableSet.univ hU (hYpo a)
  rw [cond_univ, Fintype.sum_bool, measureReal_inter_false hU] at key
  simp only [Set.univ_inter, probReal_univ, one_mul] at key
  have h0 := hterm false
  rw [show μ.real (U ⁻¹' {false}) = 1 - μ.real (U ⁻¹' {true}) by
    have := measureReal_inter_false (μ := μ) (s := Set.univ) hU
    simpa using this] at h0
  rw [key, hterm true, h0]
  unfold standardizedMean margPrev
  ring

/-- Under the assumptions of `integral_eq_standardized`, the standardized effect of the cell
means is the average treatment effect `E[Y^1] - E[Y^0]`. -/
theorem standardizedEffect_eq_ate {μ : Measure Ω} [IsProbabilityMeasure μ] {A U : Ω → Bool}
    (hA : Measurable A) (hU : Measurable U) {Y : Ω → ℝ} {Ypo : Bool → Ω → ℝ}
    (hYpo : ∀ a, Integrable (Ypo a) μ) (hcons : ∀ᵐ ω ∂μ, Y ω = Ypo (A ω) ω)
    (hexch : ∀ a u, μ (A ⁻¹' {a} ∩ U ⁻¹' {u}) ≠ 0 →
      ∫ ω, Ypo a ω ∂μ[|A ⁻¹' {a} ∩ U ⁻¹' {u}] = ∫ ω, Ypo a ω ∂μ[|U ⁻¹' {u}])
    (hpos : ∀ a u, μ (U ⁻¹' {u}) ≠ 0 → μ (A ⁻¹' {a} ∩ U ⁻¹' {u}) ≠ 0) :
    standardizedEffect (cellMean μ A U Y) (margPrev μ U) =
      ∫ ω, Ypo true ω ∂μ - ∫ ω, Ypo false ω ∂μ := by
  rw [standardizedEffect_eq_sub, integral_eq_standardized hA hU hYpo hcons hexch hpos,
    integral_eq_standardized hA hU hYpo hcons hexch hpos]

/-- Positivity in the strata of positive measure gives both arms positive measure. -/
theorem measure_arm_ne_zero {μ : Measure Ω} [IsProbabilityMeasure μ] {A U : Ω → Bool}
    (hpos : ∀ a u, μ (U ⁻¹' {u}) ≠ 0 → μ (A ⁻¹' {a} ∩ U ⁻¹' {u}) ≠ 0) (a : Bool) :
    μ (A ⁻¹' {a}) ≠ 0 := by
  have hsupp : ∃ u, μ (U ⁻¹' {u}) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hu : (Set.univ : Set Ω) = U ⁻¹' {true} ∪ U ⁻¹' {false} := by
      ext ω
      cases U ω <;> simp
    have : μ Set.univ = 0 := by
      rw [hu]
      exact measure_union_null (h true) (h false)
    simp at this
  obtain ⟨u, hu⟩ := hsupp
  exact fun h0 => hpos a u hu (measure_mono_null Set.inter_subset_left h0)

/-- The bias of the crude contrast for the average treatment effect. Under consistency,
conditional mean exchangeability given `U`, and positivity in the strata of positive measure
(the assumptions of `integral_eq_standardized`), the crude contrast
`E[Y | A = 1] - E[Y | A = 0]` minus the average treatment effect `E[Y^1] - E[Y^0]` equals the
general bias formula of VanderWeele and Arah,
`(m 1 1 - m 1 0) (π 1 - r) - (m 0 1 - m 0 0) (π 0 - r)` with cell means
`m a u = E[Y | A = a, U = u]`, prevalences `π a = P(U = 1 | A = a)`, and `r = P(U = 1)`. -/
theorem crude_sub_ate_eq {μ : Measure Ω} [IsProbabilityMeasure μ] {A U : Ω → Bool}
    (hA : Measurable A) (hU : Measurable U) {Y : Ω → ℝ} {Ypo : Bool → Ω → ℝ}
    (hY : Integrable Y μ) (hYpo : ∀ a, Integrable (Ypo a) μ)
    (hcons : ∀ᵐ ω ∂μ, Y ω = Ypo (A ω) ω)
    (hexch : ∀ a u, μ (A ⁻¹' {a} ∩ U ⁻¹' {u}) ≠ 0 →
      ∫ ω, Ypo a ω ∂μ[|A ⁻¹' {a} ∩ U ⁻¹' {u}] = ∫ ω, Ypo a ω ∂μ[|U ⁻¹' {u}])
    (hpos : ∀ a u, μ (U ⁻¹' {u}) ≠ 0 → μ (A ⁻¹' {a} ∩ U ⁻¹' {u}) ≠ 0) :
    (∫ ω, Y ω ∂μ[|A ⁻¹' {true}] - ∫ ω, Y ω ∂μ[|A ⁻¹' {false}]) -
        (∫ ω, Ypo true ω ∂μ - ∫ ω, Ypo false ω ∂μ) =
      (cellMean μ A U Y true true - cellMean μ A U Y true false) *
          (condPrev μ A U true - margPrev μ U) -
        (cellMean μ A U Y false true - cellMean μ A U Y false false) *
          (condPrev μ A U false - margPrev μ U) := by
  rw [integral_cond_eq_observedMean hA hU hY true (measure_arm_ne_zero hpos true),
    integral_cond_eq_observedMean hA hU hY false (measure_arm_ne_zero hpos false),
    ← standardizedEffect_eq_ate hA hU hYpo hcons hexch hpos]
  exact unadjustedBias_eq _ _ _

end BiasFormulas

end CausalInference
