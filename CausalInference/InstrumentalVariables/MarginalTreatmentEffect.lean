/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.Heterogeneity
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Marginal treatment effects

The latent index (generalized Roy) model and its marginal treatment effect (MTE). A unit has
potential outcomes `Y₀`, `Y₁`, a latent resistance `V` uniform on the unit interval, and an
instrument `Z` independent of `(Y₀, Y₁, V)`; it takes the treatment exactly when `V ≤ p(Z)`. The
MTE at `v` is the mean gain `E[Y₁ - Y₀ | V = v]` of the units with resistance `v`, who are
indifferent to treatment when the threshold is `v`. All the usual treatment parameters are
weighted averages of the MTE.

NICE Decision Support Unit Technical Support Document 17 (Faria, Hernandez Alava, Manca and
Wailoo, 2015, *The use of observational data to inform estimates of treatment effectiveness in
technology appraisal: methods for comparative individual patient data*) describes the MTE in
words only, in Section 2.1.2 ("the average treatment effect for those individuals who are
indifferent between receiving the treatment or not at a given value of the observable
variables"; it "can be used to construct all the treatment effects defined above") and
Section 2.4.1 (local instrumental variable methods estimate the MTE, and aggregate parameters
such as the ATE are weighted averages of it). It prints no formula, no index model and no
weights; it refers to Heckman and Vytlacil (2007, *Econometric evaluation of social programs,
part II*, Handbook of Econometrics). The formal statements below follow Heckman and Vytlacil
(1999, *Local instrumental variables and latent variable models for identifying and bounding
treatment effects*; 2005, *Structural equations, treatment effects, and econometric policy
evaluation*); the LATE theorem used for the link is that of Imbens and Angrist (1994). No
covariates are modeled: the MTE is `E[Y₁ - Y₀ | V = v]`, not `E[Y₁ - Y₀ | X = x, V = v]`.

## Setting

`CausalInference.LatentIndexModel` holds measurable `Y₀ Y₁ V : Ω → ℝ`, an instrument
`Z : Ω → 𝒵` and thresholds `p : 𝒵 → ℝ`; the treatment is `D = 1{V ≤ p(Z)}` and the outcome
`Y = Y_D`. The assumptions are explicit hypotheses: `UniformResistance` (the law of `V` is
Lebesgue measure on `[0, 1]`), `InstrumentIndependence` (`Z` independent of `(Y₀, Y₁, V)`),
integrability of `Y₀` and `Y₁`, and, where needed, `p z ∈ [0, 1]` (then `p z` is the probability
of treatment at `z`, `LatentIndexModel.condMean_DReal`). The threshold is not given any other
role.

## Main definitions

* `LatentIndexModel.IsMTE μ m`: `m` is measurable and `E[Y₁ - Y₀ | σ(V)] = m ∘ V` almost surely.
* `LatentIndexModel.mteIntegral m q`: `∫₀^q m`.
* `LatentIndexModel.lateBetween μ q q'`: `E[Y₁ - Y₀ | q < V ≤ q']`.
* `LatentIndexModel.wald μ z z'`: the Wald ratio between two instrument values.
* `LatentIndexModel.att`, `LatentIndexModel.atu`, with weights `attWeight`, `atuWeight`,
  `lateWeight`.
* `LatentIndexModel.toIVModel`: a binary instrument latent index model as a
  `CausalInference.IVModel`.
* `IVModel.HasLatentIndex`: the potential treatments of a binary model are thresholds of one
  latent variable.

## Main results

* (b) `LatentIndexModel.exists_isMTE`, `LatentIndexModel.IsMTE.ae_eq` (existence, and uniqueness
  almost everywhere on the unit interval), `LatentIndexModel.IsMTE.setIntegral_preimage`
  (`∫_{V ∈ B} (Y₁ - Y₀) = ∫_{B ∩ (0, 1]} m`), `LatentIndexModel.IsMTE.integral_gain`
  (`ATE = ∫₀¹ MTE`).
* (c) `LatentIndexModel.IsMTE.wald_eq`: for `0 ≤ p z < p z' ≤ 1`, the Wald ratio between `z` and
  `z'` is the average of the MTE over `(p z, p z']` and the LATE of the units with resistance in
  that band. `LatentIndexModel.toIVModel_lateAssumptions`: with a binary instrument the index
  model satisfies `IVModel.LATEAssumptions`, in particular `IVModel.Monotonicity`
  (`LatentIndexModel.toIVModel_monotonicity`); `LatentIndexModel.IsMTE.toIVModel_wald_eq`
  combines the LATE theorem `IVModel.LATEAssumptions.wald_eq` with the MTE form.
* (d) `LatentIndexModel.IsMTE.condExp_Y`: `E[Y | p(Z)] = E[Y₀] + ∫₀^{p(Z)} MTE` almost surely,
  with no regularity; `LatentIndexModel.IsMTE.hasDerivAt_outcomeCurve`: the curve has derivative
  `MTE(q)` at every interior `q` where the version `m` is continuous (local instrumental
  variables).
* (e) `LatentIndexModel.IsMTE.att_eq` (weight `P(p(Z) ≥ v) / P(D = 1)`),
  `LatentIndexModel.IsMTE.atu_eq` (weight `P(p(Z) < v) / P(D = 0)`),
  `LatentIndexModel.integral_attWeight`, `LatentIndexModel.integral_atuWeight` (the weights
  integrate to one), `LatentIndexModel.IsMTE.ate_eq_weighted` (weight one),
  `LatentIndexModel.IsMTE.lateBetween_eq_weighted`, and
  `LatentIndexModel.IsMTE.collapse_of_const` (a constant MTE makes all of them equal).
* (f) `IVModel.HasLatentIndex.monotone`, `IVCounterexample.modelA_not_hasLatentIndex` and
  `IVCounterexample.modelA_wald_ne_weighted`: the defier countermodel of
  `CausalInference.InstrumentalVariables.Counterexamples` has two-way flows, so no latent index
  representation, and its Wald ratio `-2` is no nonnegative average of its unit effects (all at
  least `1`). The worked model with nonconstant MTE is in
  `CausalInference.InstrumentalVariables.MarginalTreatmentEffectExamples`.

The converse direction of Vytlacil (2002, *Independence, monotonicity, and latent index models:
an equivalence result*), that monotonicity and independence yield a latent index
representation, is not formalized.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

/-- A latent index (generalized Roy) model on a sample space `Ω` with instrument values in `𝒵`:
measurable potential outcomes `Y₀`, `Y₁`, a measurable latent resistance `V`, a measurable
instrument `Z`, and a measurable threshold function `p`. A unit takes the treatment exactly when
its resistance does not exceed the threshold set by its instrument value,
`D = 1{V ≤ p(Z)}` (`LatentIndexModel.D`). The distributional assumptions (uniform resistance,
independence of the instrument) are separate predicates. -/
structure LatentIndexModel (Ω 𝒵 : Type*) [MeasurableSpace Ω] [MeasurableSpace 𝒵] where
  /-- The potential outcome without treatment. -/
  Y₀ : Ω → ℝ
  /-- The potential outcome with treatment. -/
  Y₁ : Ω → ℝ
  /-- The latent resistance to treatment. -/
  V : Ω → ℝ
  /-- The instrument. -/
  Z : Ω → 𝒵
  /-- The threshold set by each instrument value. -/
  p : 𝒵 → ℝ
  measurable_Y₀ : Measurable Y₀
  measurable_Y₁ : Measurable Y₁
  measurable_V : Measurable V
  measurable_Z : Measurable Z
  measurable_p : Measurable p

namespace LatentIndexModel

variable {Ω 𝒵 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒵] (M : LatentIndexModel Ω 𝒵)

/-- The treatment taken: `D ω = 1{V ω ≤ p (Z ω)}`. -/
noncomputable def D (ω : Ω) : Bool := decide (M.V ω ≤ M.p (M.Z ω))

/-- The observed outcome: `Y₁` for treated units and `Y₀` for untreated units. -/
noncomputable def Y (ω : Ω) : ℝ := if M.D ω then M.Y₁ ω else M.Y₀ ω

/-- The unit-level gain from treatment, `Y₁ - Y₀`. -/
def gain (ω : Ω) : ℝ := M.Y₁ ω - M.Y₀ ω

/-- The latent variables of a unit: both potential outcomes and the resistance. -/
def latent (ω : Ω) : ℝ × ℝ × ℝ := (M.Y₀ ω, M.Y₁ ω, M.V ω)

/-- The resistance `V` has the uniform law on the unit interval. -/
def UniformResistance (μ : Measure Ω) : Prop := μ.map M.V = volume.restrict (Icc 0 1)

/-- The instrument `Z` is independent of the latent vector `(Y₀, Y₁, V)`. -/
def InstrumentIndependence (μ : Measure Ω) : Prop := IndepFun M.Z M.latent μ

/-- `m` is a marginal treatment effect function: `m` is measurable and
`E[Y₁ - Y₀ | V] = m ∘ V` almost surely, where the conditional expectation is taken with respect
to the sigma algebra generated by `V`. A version of the conditional expectation exists and is
unique only up to null sets, so `m` is determined only almost everywhere on the unit interval
(`LatentIndexModel.IsMTE.ae_eq`, `LatentIndexModel.exists_isMTE`). For a non-integrable gain the
conditional expectation is `0` by convention; every theorem below assumes the gain integrable. -/
def IsMTE (μ : Measure Ω) (m : ℝ → ℝ) : Prop :=
  Measurable m ∧ μ[M.gain | MeasurableSpace.comap M.V inferInstance] =ᵐ[μ] m ∘ M.V

/-- The cumulative marginal treatment effect `∫₀^q m(v) dv`, with `m` cut off outside the unit
interval (for `q` in the unit interval the cutoff changes nothing). -/
noncomputable def mteIntegral (m : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..q, (Ioc 0 1).indicator m v

/-! ### Measurability -/

theorem measurable_gain : Measurable M.gain := M.measurable_Y₁.sub M.measurable_Y₀

theorem measurable_latent : Measurable M.latent :=
  M.measurable_Y₀.prodMk (M.measurable_Y₁.prodMk M.measurable_V)

theorem measurableSet_D : MeasurableSet {ω | M.D ω = true} := by
  simp only [D, decide_eq_true_eq]
  exact measurableSet_le M.measurable_V (M.measurable_p.comp M.measurable_Z)

theorem measurable_D : Measurable M.D :=
  measurable_to_countable' fun b ↦ by
    cases b
    · have : M.D ⁻¹' {false} = {ω | M.D ω = true}ᶜ := by ext ω; simp
      rw [this]; exact M.measurableSet_D.compl
    · exact M.measurableSet_D

theorem measurable_Y : Measurable M.Y :=
  Measurable.ite M.measurableSet_D M.measurable_Y₁ M.measurable_Y₀

/-! ### The uniform law of the resistance -/

theorem restrict_Icc_eq_restrict_Ioc :
    (volume.restrict (Icc (0 : ℝ) 1)) = volume.restrict (Ioc 0 1) :=
  (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm

variable {M} {μ : Measure Ω}

theorem UniformResistance.map_eq (hU : M.UniformResistance μ) :
    μ.map M.V = volume.restrict (Ioc 0 1) := by
  rw [hU, restrict_Icc_eq_restrict_Ioc]

/-- Under the uniform law, `P(V ≤ q) = q` for `q` in the unit interval. -/
theorem UniformResistance.measureReal_le (hU : M.UniformResistance μ) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) : μ.real {ω | M.V ω ≤ q} = q := by
  have h : {ω | M.V ω ≤ q} = M.V ⁻¹' Iic q := rfl
  rw [h, measureReal_def, ← Measure.map_apply M.measurable_V measurableSet_Iic, hU,
    Measure.restrict_apply measurableSet_Iic]
  have : Iic q ∩ Icc 0 1 = Icc 0 q := by
    ext v; simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hq.2⟩
  rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hq.1])]
  ring

/-! ### The marginal treatment effect -/

theorem comap_V_le :
    MeasurableSpace.comap M.V inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
  M.measurable_V.comap_le

/-- **The defining property of the MTE in integrated form.** If `V` is uniform on the unit
interval, the gain is integrable and `m` is a marginal treatment effect function, then for every
Borel set `B`, `∫_{V ∈ B} (Y₁ - Y₀) dμ = ∫_{B ∩ (0, 1]} m(v) dv`. -/
theorem IsMTE.setIntegral_preimage [IsFiniteMeasure μ] (hU : M.UniformResistance μ) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m)
    (hint : Integrable M.gain μ) {B : Set ℝ} (hB : MeasurableSet B) :
    ∫ ω in M.V ⁻¹' B, M.gain ω ∂μ = ∫ v in B ∩ Ioc 0 1, m v := by
  rw [← setIntegral_condExp comap_V_le hint ⟨B, hB, rfl⟩,
    setIntegral_congr_ae (M.measurable_V hB) (hm.2.mono fun ω h _ ↦ h)]
  change ∫ x in M.V ⁻¹' B, m (M.V x) ∂μ = _
  rw [← setIntegral_map hB hm.1.aestronglyMeasurable M.measurable_V.aemeasurable, hU.map_eq,
    Measure.restrict_restrict hB]

/-- A marginal treatment effect function is integrable on the unit interval. -/
theorem IsMTE.integrableOn (hU : M.UniformResistance μ) {m : ℝ → ℝ} (hm : M.IsMTE μ m) :
    IntegrableOn m (Ioc 0 1) := by
  have h : Integrable (m ∘ M.V) μ := integrable_condExp.congr hm.2
  rw [IntegrableOn, ← hU.map_eq]
  exact (integrable_map_measure hm.1.aestronglyMeasurable M.measurable_V.aemeasurable).2 h

/-- **Uniqueness of the MTE.** Two marginal treatment effect functions agree almost everywhere
on the unit interval (Lebesgue measure). No pointwise statement about `m` is identified without
a further choice of version. -/
theorem IsMTE.ae_eq (hU : M.UniformResistance μ) {m₁ m₂ : ℝ → ℝ} (h₁ : M.IsMTE μ m₁)
    (h₂ : M.IsMTE μ m₂) : m₁ =ᵐ[volume.restrict (Ioc 0 1)] m₂ := by
  rw [← hU.map_eq]
  exact (ae_map_iff M.measurable_V.aemeasurable (measurableSet_eq_fun h₁.1 h₂.1)).2
    (h₁.2.symm.trans h₂.2)

/-- **Existence of the MTE.** The conditional expectation of the gain given `V` factors through
`V` by a measurable function (Doob and Dynkin factorization), which is a marginal treatment
effect function. -/
theorem exists_isMTE (M : LatentIndexModel Ω 𝒵) (μ : Measure Ω) : ∃ m : ℝ → ℝ, M.IsMTE μ m := by
  obtain ⟨m, hm, h⟩ := (stronglyMeasurable_condExp (f := M.gain) (μ := μ)
    (m := MeasurableSpace.comap M.V inferInstance)).measurable.exists_eq_measurable_comp
  exact ⟨m, hm, by rw [← h]⟩

/-- **The average treatment effect is the integral of the MTE**:
`E[Y₁ - Y₀] = ∫₀¹ MTE(v) dv`. -/
theorem IsMTE.integral_gain [IsFiniteMeasure μ] (hU : M.UniformResistance μ) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m)
    (hint : Integrable M.gain μ) : ∫ ω, M.gain ω ∂μ = ∫ v in Ioc 0 1, m v := by
  have h := hm.setIntegral_preimage hU hint MeasurableSet.univ
  rwa [preimage_univ, setIntegral_univ, univ_inter] at h

/-- The cumulative MTE as a set integral: `∫₀^q m = ∫_{(-∞, q] ∩ (0, 1]} m`, for every `q`. -/
theorem mteIntegral_eq (m : ℝ → ℝ) (q : ℝ) :
    mteIntegral m q = ∫ v in Iic q ∩ Ioc 0 1, m v := by
  rcases le_or_gt 0 q with hq | hq
  · rw [mteIntegral, intervalIntegral.integral_of_le hq, setIntegral_indicator measurableSet_Ioc]
    have e : Ioc 0 q ∩ Ioc (0 : ℝ) 1 = Iic q ∩ Ioc 0 1 := by
      ext v; simp only [mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨h'.1, h⟩, h'⟩
    rw [e]
  · rw [mteIntegral, intervalIntegral.integral_of_ge hq.le, setIntegral_indicator measurableSet_Ioc]
    have h1 : Ioc q 0 ∩ Ioc (0 : ℝ) 1 = ∅ := by
      ext v; simp only [mem_inter_iff, mem_Ioc, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, h⟩, h', _⟩; linarith
    have h2 : Iic q ∩ Ioc (0 : ℝ) 1 = ∅ := by
      ext v; simp only [mem_inter_iff, mem_Ioc, mem_Iic, mem_empty_iff_false, iff_false]
      rintro ⟨h, h', _⟩; linarith
    rw [h1, h2, Measure.restrict_empty, integral_zero_measure, neg_zero]

/-- `∫_{V ≤ q} (Y₁ - Y₀) dμ = ∫₀^q MTE(v) dv`, for every `q`. -/
theorem IsMTE.setIntegral_le [IsFiniteMeasure μ] (hU : M.UniformResistance μ) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m)
    (hint : Integrable M.gain μ) (q : ℝ) :
    ∫ ω in {ω | M.V ω ≤ q}, M.gain ω ∂μ = mteIntegral m q := by
  rw [mteIntegral_eq, ← hm.setIntegral_preimage hU hint measurableSet_Iic]
  rfl

/-- The MTE cut off outside the unit interval is integrable on the real line. -/
theorem IsMTE.integrable_indicator (hU : M.UniformResistance μ) {m : ℝ → ℝ} (hm : M.IsMTE μ m) :
    Integrable ((Ioc 0 1).indicator m) :=
  (hm.integrableOn hU).integrable_indicator measurableSet_Ioc

/-- For `0 ≤ q ≤ q' ≤ 1`: `∫₀^{q'} m - ∫₀^q m = ∫_{(q, q']} m`. -/
theorem mteIntegral_sub {m : ℝ → ℝ} (hm : Integrable ((Ioc 0 1).indicator m)) {q q' : ℝ}
    (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1) :
    mteIntegral m q' - mteIntegral m q = ∫ v in Ioc q q', m v := by
  have hsub : Ioc q q' ⊆ Ioc (0 : ℝ) 1 := fun v hv ↦ ⟨hq.trans_lt hv.1, hv.2.trans hq'⟩
  rw [mteIntegral, mteIntegral, intervalIntegral.integral_interval_sub_left
    (hm.intervalIntegrable) (hm.intervalIntegrable), intervalIntegral.integral_of_le hqq,
    setIntegral_indicator measurableSet_Ioc, inter_eq_left.2 hsub]

/-! ### Conditioning on the instrument -/

/-- The conditional mean `E[f | Z ∈ S]`: the integral of `f` against `μ[|Z ∈ S]`. -/
noncomputable def condMean (μ : Measure Ω) (f : Ω → ℝ) (S : Set 𝒵) : ℝ :=
  ∫ ω, f ω ∂μ[|M.Z ⁻¹' S]

/-- The treatment coded as a real number. -/
noncomputable def DReal (ω : Ω) : ℝ := IVModel.boolToReal (M.D ω)

/-- The local average treatment effect of the units with resistance in `(q, q']`, that is,
`E[Y₁ - Y₀ | q < V ≤ q']`. For two instrument values `z`, `z'` with `p z < p z'` these are the
units moved into treatment by the change from `z` to `z'` (`LatentIndexModel.D_eq_D_iff`). -/
noncomputable def lateBetween (μ : Measure Ω) (q q' : ℝ) : ℝ :=
  ∫ ω, M.gain ω ∂μ[|M.V ⁻¹' Ioc q q']

/-- Under instrument independence and `P(Z ∈ S) ≠ 0`, the law of the latent vector given
`Z ∈ S` is its unconditional law. -/
theorem InstrumentIndependence.map_latent_cond [IsFiniteMeasure μ]
    (hI : M.InstrumentIndependence μ) {S : Set 𝒵} (hS : MeasurableSet S)
    (hS0 : μ (M.Z ⁻¹' S) ≠ 0) : (μ[|M.Z ⁻¹' S]).map M.latent = μ.map M.latent := by
  ext t ht
  rw [Measure.map_apply M.measurable_latent ht, Measure.map_apply M.measurable_latent ht,
    cond_apply (M.measurable_Z hS),
    indepFun_iff_measure_inter_preimage_eq_mul.1 hI _ _ hS ht,
    ← mul_assoc, ENNReal.inv_mul_cancel hS0 (measure_ne_top _ _), one_mul]

/-- Under instrument independence and `P(Z ∈ S) ≠ 0`, the conditional mean given `Z ∈ S` of a
measurable function of the latent vector is its unconditional mean. -/
theorem InstrumentIndependence.condMean_latent [IsFiniteMeasure μ]
    (hI : M.InstrumentIndependence μ) {S : Set 𝒵} (hS : MeasurableSet S)
    (hS0 : μ (M.Z ⁻¹' S) ≠ 0) {φ : ℝ × ℝ × ℝ → ℝ} (hφ : Measurable φ) :
    M.condMean μ (fun ω ↦ φ (M.latent ω)) S = ∫ ω, φ (M.latent ω) ∂μ := by
  rw [condMean, ← integral_map M.measurable_latent.aemeasurable hφ.aestronglyMeasurable,
    hI.map_latent_cond hS hS0,
    integral_map M.measurable_latent.aemeasurable hφ.aestronglyMeasurable]

theorem condMean_congr {f g : Ω → ℝ} {S : Set 𝒵} (hS : MeasurableSet S)
    (h : ∀ ω ∈ M.Z ⁻¹' S, f ω = g ω) : M.condMean μ f S = M.condMean μ g S :=
  integral_congr_ae ((ae_cond_mem (M.measurable_Z hS)).mono h)

/-- On the units whose instrument value has threshold `q`, the observed outcome is
`Y₀ + 1{V ≤ q} (Y₁ - Y₀)`. -/
theorem Y_eq_of_p_eq {q : ℝ} {ω : Ω} (h : M.p (M.Z ω) = q) :
    M.Y ω = M.Y₀ ω + {ω | M.V ω ≤ q}.indicator M.gain ω := by
  by_cases hv : M.V ω ≤ q
  · have : M.D ω = true := by simp [D, h, hv]
    simp [Y, this, Set.indicator, hv, gain]
  · have : M.D ω = false := by simp [D, h, hv]
    simp [Y, this, Set.indicator, hv]

/-- **The mean outcome given the instrument.** Under uniform resistance, instrument
independence and integrable potential outcomes, for a set `S` of instrument values of positive
probability on which the threshold equals `q`:
`E[Y | Z ∈ S] = E[Y₀] + ∫₀^q MTE(v) dv`. -/
theorem condMean_Y [IsFiniteMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) {m : ℝ → ℝ} (hm : M.IsMTE μ m)
    (h₀ : Integrable M.Y₀ μ) (h₁ : Integrable M.Y₁ μ) {S : Set 𝒵} (hS : MeasurableSet S)
    (hS0 : μ (M.Z ⁻¹' S) ≠ 0) {q : ℝ} (hpS : ∀ z ∈ S, M.p z = q) :
    M.condMean μ M.Y S = ∫ ω, M.Y₀ ω ∂μ + mteIntegral m q := by
  have hg : Integrable M.gain μ := h₁.sub h₀
  set φ : ℝ × ℝ × ℝ → ℝ := fun w ↦ w.1 + {w : ℝ × ℝ × ℝ | w.2.2 ≤ q}.indicator
    (fun w ↦ w.2.1 - w.1) w with hφdef
  have hφ : Measurable φ :=
    measurable_fst.add (((measurable_fst.comp measurable_snd).sub measurable_fst).indicator
      (measurableSet_le (measurable_snd.comp measurable_snd) measurable_const))
  rw [M.condMean_congr (g := fun ω ↦ φ (M.latent ω)) hS fun ω hω ↦ ?_,
    hI.condMean_latent hS hS0 hφ]
  · have e : (fun ω ↦ φ (M.latent ω)) = fun ω ↦ M.Y₀ ω + {ω | M.V ω ≤ q}.indicator M.gain ω := by
      funext ω; simp only [hφdef, latent, Set.indicator, mem_ofPred_eq, gain]
    rw [e, integral_add h₀ (hg.indicator (measurableSet_le M.measurable_V measurable_const)),
      integral_indicator (measurableSet_le M.measurable_V measurable_const),
      hm.setIntegral_le hU hg]
  · rw [M.Y_eq_of_p_eq (hpS _ hω)]
    simp only [hφdef, latent, Set.indicator, mem_ofPred_eq, gain]

/-- **The selection probability given the instrument.** Under uniform resistance and instrument
independence, for a set `S` of instrument values of positive probability on which the threshold
equals `q ∈ [0, 1]`: `P(D = 1 | Z ∈ S) = q`. So the threshold `p(z)` is the probability of
treatment at instrument value `z`. -/
theorem condMean_DReal [IsFiniteMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) {S : Set 𝒵} (hS : MeasurableSet S)
    (hS0 : μ (M.Z ⁻¹' S) ≠ 0) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hpS : ∀ z ∈ S, M.p z = q) :
    M.condMean μ M.DReal S = q := by
  set φ : ℝ × ℝ × ℝ → ℝ := {w : ℝ × ℝ × ℝ | w.2.2 ≤ q}.indicator 1 with hφdef
  have hφ : Measurable φ :=
    measurable_const.indicator (measurableSet_le (measurable_snd.comp measurable_snd)
      measurable_const)
  rw [M.condMean_congr (g := fun ω ↦ φ (M.latent ω)) hS fun ω hω ↦ ?_,
    hI.condMean_latent hS hS0 hφ]
  · have e : (fun ω ↦ φ (M.latent ω)) = {ω | M.V ω ≤ q}.indicator 1 := by
      funext ω; simp only [hφdef, latent, Set.indicator, mem_ofPred_eq, Pi.one_apply]
    rw [e, integral_indicator_one (measurableSet_le M.measurable_V measurable_const),
      hU.measureReal_le hq]
  · have h := hpS _ hω
    by_cases hv : M.V ω ≤ q
    · have : M.D ω = true := by simp [D, h, hv]
      simp [DReal, this, hφdef, latent, hv]
    · have : M.D ω = false := by simp [D, h, hv]
      simp [DReal, this, hφdef, latent, hv]

/-- Under uniform resistance, `P(q < V ≤ q') = q' - q` for `0 ≤ q ≤ q' ≤ 1`. -/
theorem UniformResistance.measureReal_Ioc (hU : M.UniformResistance μ) {q q' : ℝ}
    (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ 1) : μ.real (M.V ⁻¹' Ioc q q') = q' - q := by
  have hsub : Ioc q q' ⊆ Ioc (0 : ℝ) 1 := fun v hv ↦ ⟨hq.trans_lt hv.1, hv.2.trans hq'⟩
  rw [measureReal_def, ← Measure.map_apply M.measurable_V measurableSet_Ioc, hU.map_eq,
    Measure.restrict_apply measurableSet_Ioc, inter_eq_left.2 hsub, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith)]

/-- **The LATE of a resistance band is the average MTE over the band**: for
`0 ≤ q < q' ≤ 1`, `E[Y₁ - Y₀ | q < V ≤ q'] = (∫_{(q, q']} MTE(v) dv) / (q' - q)`. -/
theorem IsMTE.lateBetween_eq [IsFiniteMeasure μ] (hU : M.UniformResistance μ) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m) (hint : Integrable M.gain μ) {q q' : ℝ} (hq : 0 ≤ q) (hqq : q < q')
    (hq' : q' ≤ 1) : M.lateBetween μ q q' = (∫ v in Ioc q q', m v) / (q' - q) := by
  have hsub : Ioc q q' ⊆ Ioc (0 : ℝ) 1 := fun v hv ↦ ⟨hq.trans_lt hv.1, hv.2.trans hq'⟩
  rw [lateBetween, IVModel.integral_cond_eq_inv_mul, hU.measureReal_Ioc hq hqq.le hq',
    hm.setIntegral_preimage hU hint measurableSet_Ioc, inter_eq_left.2 hsub, div_eq_inv_mul]

/-! ### The Wald ratio between two instrument values -/

variable (M) in
/-- The Wald ratio between two instrument values `z` and `z'`:
`(E[Y | Z = z'] - E[Y | Z = z]) / (P(D = 1 | Z = z') - P(D = 1 | Z = z))`. -/
noncomputable def wald (μ : Measure Ω) (z z' : 𝒵) : ℝ :=
  (M.condMean μ M.Y {z'} - M.condMean μ M.Y {z}) /
    (M.condMean μ M.DReal {z'} - M.condMean μ M.DReal {z})

/-- **The index structure implies monotonicity.** If `p z ≤ p z'`, every unit treated at
instrument value `z` is treated at `z'`. -/
theorem decide_le_mono {z z' : 𝒵} (h : M.p z ≤ M.p z') (ω : Ω) :
    decide (M.V ω ≤ M.p z) ≤ decide (M.V ω ≤ M.p z') := by
  by_cases h1 : M.V ω ≤ M.p z
  · simp [h1, h1.trans h]
  · simp [h1]

/-- The units moved into treatment by the change from `z` to `z'` are those with resistance in
`(p z, p z']`. -/
theorem decide_le_iff {z z' : 𝒵} {ω : Ω} :
    (decide (M.V ω ≤ M.p z) = false ∧ decide (M.V ω ≤ M.p z') = true) ↔
      M.V ω ∈ Ioc (M.p z) (M.p z') := by
  simp [mem_Ioc]

/-- **The Wald ratio is the average MTE over the band of resistances it moves** (the local
instrumental variable reading of the LATE; Heckman and Vytlacil, 2005, *Structural equations,
treatment effects, and econometric policy evaluation*). Under uniform resistance, instrument
independence and integrable potential outcomes, for two instrument values of positive
probability with `0 ≤ p z < p z' ≤ 1`:
`Wald(z, z') = (∫_{(p z, p z']} MTE(v) dv) / (p z' - p z) = E[Y₁ - Y₀ | p z < V ≤ p z']`. -/
theorem IsMTE.wald_eq [IsFiniteMeasure μ] [MeasurableSingletonClass 𝒵]
    (hU : M.UniformResistance μ) (hI : M.InstrumentIndependence μ) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m) (h₀ : Integrable M.Y₀ μ) (h₁ : Integrable M.Y₁ μ) {z z' : 𝒵}
    (hz : μ (M.Z ⁻¹' {z}) ≠ 0) (hz' : μ (M.Z ⁻¹' {z'}) ≠ 0) (hp : 0 ≤ M.p z)
    (hpp : M.p z < M.p z') (hp' : M.p z' ≤ 1) :
    M.wald μ z z' = (∫ v in Ioc (M.p z) (M.p z'), m v) / (M.p z' - M.p z) ∧
      M.wald μ z z' = M.lateBetween μ (M.p z) (M.p z') := by
  have hwald : M.wald μ z z' = (∫ v in Ioc (M.p z) (M.p z'), m v) / (M.p z' - M.p z) := by
    rw [wald, M.condMean_Y hU hI hm h₀ h₁ (measurableSet_singleton z) hz (fun _ h ↦ by rw [h]),
      M.condMean_Y hU hI hm h₀ h₁ (measurableSet_singleton z') hz' (fun _ h ↦ by rw [h]),
      M.condMean_DReal hU hI (measurableSet_singleton z) hz ⟨hp, hpp.le.trans hp'⟩
        (fun _ h ↦ by rw [h]),
      M.condMean_DReal hU hI (measurableSet_singleton z') hz' ⟨hp.trans hpp.le, hp'⟩
        (fun _ h ↦ by rw [h]),
      add_sub_add_left_eq_sub, mteIntegral_sub (hm.integrable_indicator hU) hp hpp.le hp']
  exact ⟨hwald, hwald.trans (hm.lateBetween_eq hU (h₁.sub h₀) hp hpp hp').symm⟩

/-! ### Integrating over the instrument -/

/-- **Integration over an independent instrument.** Under instrument independence, for a
jointly measurable `F` dominated by an integrable function of the latent vector,
`∫ F(Z, (Y₀, Y₁, V)) dμ = ∫ (∫ F(z, (Y₀, Y₁, V)) dμ) d(law of Z)(z)`. -/
theorem InstrumentIndependence.integral_eq [IsProbabilityMeasure μ]
    (hI : M.InstrumentIndependence μ) {F : 𝒵 × (ℝ × ℝ × ℝ) → ℝ} (hF : Measurable F)
    {g : ℝ × ℝ × ℝ → ℝ} (hgm : Measurable g) (hg : Integrable (fun ω ↦ g (M.latent ω)) μ)
    (hFg : ∀ z w, ‖F (z, w)‖ ≤ g w) :
    ∫ ω, F (M.Z ω, M.latent ω) ∂μ = ∫ z, (∫ ω, F (z, M.latent ω) ∂μ) ∂(μ.map M.Z) := by
  have hmap : μ.map (fun ω ↦ (M.Z ω, M.latent ω)) = (μ.map M.Z).prod (μ.map M.latent) :=
    (indepFun_iff_map_prod_eq_prod_map_map M.measurable_Z.aemeasurable
      M.measurable_latent.aemeasurable).1 hI
  have hg' : Integrable g (μ.map M.latent) :=
    (integrable_map_measure hgm.aestronglyMeasurable M.measurable_latent.aemeasurable).2 hg
  have hint : Integrable F ((μ.map M.Z).prod (μ.map M.latent)) := by
    refine Integrable.mono' (((integrable_const (1 : ℝ)).mul_prod hg').congr ?_)
      hF.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ hFg x.1 x.2)
    exact Filter.Eventually.of_forall fun x ↦ one_mul _
  have e : ∫ ω, F (M.Z ω, M.latent ω) ∂μ = ∫ x, F x ∂(μ.map fun ω ↦ (M.Z ω, M.latent ω)) :=
    (integral_map (M.measurable_Z.prodMk M.measurable_latent).aemeasurable
      hF.aestronglyMeasurable).symm
  rw [e, hmap, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  exact (integral_map M.measurable_latent.aemeasurable
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)

/-- **The exchange of the instrument and resistance integrals.** For a finite measure `ν` on
the instrument values, a measurable threshold `p` and a measurable `m` integrable on `(0, 1]`:
`∫ (∫₀^{p z} m) dν(z) = ∫_{(0, 1]} ν(p ≥ v) m(v) dv`. -/
theorem integral_mteIntegral_comp {ν : Measure 𝒵} [IsFiniteMeasure ν] {p : 𝒵 → ℝ}
    (hp : Measurable p) {m : ℝ → ℝ} (hmeas : Measurable m) (hm : IntegrableOn m (Ioc 0 1)) :
    ∫ z, mteIntegral m (p z) ∂ν = ∫ v in Ioc 0 1, ν.real {z | v ≤ p z} * m v := by
  set G : 𝒵 → ℝ → ℝ := fun z v ↦ {z | v ≤ p z}.indicator (fun _ ↦ m v) z with hG
  have h1 : ∀ z, mteIntegral m (p z) = ∫ v in Ioc 0 1, G z v := by
    intro z
    rw [mteIntegral_eq, ← Measure.restrict_restrict measurableSet_Iic,
      ← integral_indicator measurableSet_Iic]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
    simp only [hG, Set.indicator, mem_Iic, mem_ofPred_eq]
  have hGm : Measurable (Function.uncurry G) := by
    refine Measurable.ite (measurableSet_le measurable_snd (hp.comp measurable_fst))
      (hmeas.comp measurable_snd) measurable_const
  have hint : Integrable (Function.uncurry G) (ν.prod (volume.restrict (Ioc 0 1))) := by
    refine Integrable.mono' (g := fun x : 𝒵 × ℝ ↦ ‖m x.2‖)
      (((integrable_const (1 : ℝ)).mul_prod hm.norm).congr ?_)
      hGm.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ ?_)
    · exact Filter.Eventually.of_forall fun x ↦ one_mul _
    · simp only [Function.uncurry, hG, Set.indicator]
      split_ifs <;> simp
  simp_rw [h1]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
  simp only [hG]
  rw [integral_indicator_const _ (measurableSet_le measurable_const hp), smul_eq_mul]

/-- The outcome over an instrument set: under uniform resistance, instrument independence and
integrable potential outcomes, for every measurable set `S` of instrument values,
`E[Y 1{Z ∈ S}] = ∫_S (E[Y₀] + ∫₀^{p z} MTE) d(law of Z)(z)`. -/
theorem IsMTE.integral_indicator_Y [IsProbabilityMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) {m : ℝ → ℝ} (hm : M.IsMTE μ m)
    (h₀ : Integrable M.Y₀ μ) (h₁ : Integrable M.Y₁ μ) {S : Set 𝒵} (hS : MeasurableSet S) :
    ∫ ω, (M.Z ⁻¹' S).indicator M.Y ω ∂μ =
      ∫ z, S.indicator (fun z ↦ ∫ ω, M.Y₀ ω ∂μ + mteIntegral m (M.p z)) z ∂(μ.map M.Z) := by
  have hg : Integrable M.gain μ := h₁.sub h₀
  set F : 𝒵 × (ℝ × ℝ × ℝ) → ℝ := (Prod.fst ⁻¹' S).indicator fun x ↦
    x.2.1 + (if x.2.2.2 ≤ M.p x.1 then x.2.2.1 - x.2.1 else 0) with hF
  have hFm : Measurable F := by
    refine Measurable.indicator (Measurable.add
      (measurable_fst.comp measurable_snd) (Measurable.ite ?_ ?_ measurable_const))
      (measurable_fst hS)
    · exact measurableSet_le (measurable_snd.comp (measurable_snd.comp measurable_snd))
        (M.measurable_p.comp measurable_fst)
    · exact (measurable_fst.comp (measurable_snd.comp measurable_snd)).sub
        (measurable_fst.comp measurable_snd)
  have hgm : Measurable fun w : ℝ × ℝ × ℝ ↦ ‖w.1‖ + ‖w.2.1 - w.1‖ :=
    measurable_fst.norm.add ((measurable_fst.comp measurable_snd).sub measurable_fst).norm
  have hgi : Integrable (fun ω ↦ ‖(M.latent ω).1‖ + ‖(M.latent ω).2.1 - (M.latent ω).1‖) μ :=
    h₀.norm.add hg.norm
  have hb : ∀ z w, ‖F (z, w)‖ ≤ ‖w.1‖ + ‖w.2.1 - w.1‖ := by
    intro z w
    by_cases hz : z ∈ S
    · rw [hF, Set.indicator_of_mem (show (z, w) ∈ Prod.fst ⁻¹' S from hz)]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      split_ifs
      · exact le_rfl
      · simp
    · rw [hF, Set.indicator_of_notMem (show (z, w) ∉ Prod.fst ⁻¹' S from hz), norm_zero]
      positivity
  have key := hI.integral_eq hFm hgm hgi hb
  have hL : (fun ω ↦ F (M.Z ω, M.latent ω)) = (M.Z ⁻¹' S).indicator M.Y := by
    funext ω
    by_cases hz : M.Z ω ∈ S
    · rw [Set.indicator_of_mem (show ω ∈ M.Z ⁻¹' S from hz), M.Y_eq_of_p_eq rfl, hF,
        Set.indicator_of_mem (show (M.Z ω, M.latent ω) ∈ Prod.fst ⁻¹' S from hz)]
      simp only [latent, Set.indicator, gain, mem_ofPred_eq]
      by_cases hv : M.V ω ≤ M.p (M.Z ω) <;> simp [hv]
    · rw [Set.indicator_of_notMem (show ω ∉ M.Z ⁻¹' S from hz), hF,
        Set.indicator_of_notMem (show (M.Z ω, M.latent ω) ∉ Prod.fst ⁻¹' S from hz)]
  rw [← hL, key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  by_cases hz : z ∈ S
  · rw [Set.indicator_of_mem hz]
    have e : (fun ω ↦ F (z, M.latent ω)) =
        fun ω ↦ M.Y₀ ω + {ω | M.V ω ≤ M.p z}.indicator M.gain ω := by
      funext ω
      rw [hF, Set.indicator_of_mem (show (z, M.latent ω) ∈ Prod.fst ⁻¹' S from hz)]
      simp only [latent, Set.indicator, gain, mem_ofPred_eq]
      by_cases hv : M.V ω ≤ M.p z <;> simp [hv]
    simp only [e]
    rw [integral_add h₀ (hg.indicator (measurableSet_le M.measurable_V measurable_const)),
      integral_indicator (measurableSet_le M.measurable_V measurable_const),
      hm.setIntegral_le hU hg]
  · rw [Set.indicator_of_notMem hz]
    have e : (fun ω ↦ F (z, M.latent ω)) = fun _ ↦ 0 := by
      funext ω
      rw [hF, Set.indicator_of_notMem (show (z, M.latent ω) ∉ Prod.fst ⁻¹' S from hz)]
    simp only [e, integral_zero]

/-- The gain of the treated: under uniform resistance, instrument independence and an
integrable gain, `E[(Y₁ - Y₀) 1{D = 1}] = ∫ (∫₀^{p z} MTE) d(law of Z)(z)`. -/
theorem IsMTE.integral_indicator_treated_gain [IsProbabilityMeasure μ]
    (hU : M.UniformResistance μ) (hI : M.InstrumentIndependence μ) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m) (hg : Integrable M.gain μ) :
    ∫ ω, {ω | M.D ω = true}.indicator M.gain ω ∂μ =
      ∫ z, mteIntegral m (M.p z) ∂(μ.map M.Z) := by
  set F : 𝒵 × (ℝ × ℝ × ℝ) → ℝ := fun x ↦
    if x.2.2.2 ≤ M.p x.1 then x.2.2.1 - x.2.1 else 0 with hF
  have hFm : Measurable F := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_le (measurable_snd.comp (measurable_snd.comp measurable_snd))
        (M.measurable_p.comp measurable_fst)
    · exact (measurable_fst.comp (measurable_snd.comp measurable_snd)).sub
        (measurable_fst.comp measurable_snd)
  have hgm : Measurable fun w : ℝ × ℝ × ℝ ↦ ‖w.2.1 - w.1‖ :=
    ((measurable_fst.comp measurable_snd).sub measurable_fst).norm
  have hb : ∀ z w, ‖F (z, w)‖ ≤ ‖w.2.1 - w.1‖ := by
    intro z w
    simp only [hF]
    split_ifs
    · exact le_rfl
    · simp
  have key := hI.integral_eq hFm hgm hg.norm hb
  have hL : (fun ω ↦ F (M.Z ω, M.latent ω)) = {ω | M.D ω = true}.indicator M.gain := by
    funext ω
    simp [hF, Set.indicator, latent, D, gain]
  rw [← hL, key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  have e : (fun ω ↦ F (z, M.latent ω)) = {ω | M.V ω ≤ M.p z}.indicator M.gain := by
    funext ω; simp [hF, latent, Set.indicator, gain]
  simp only [e]
  rw [integral_indicator (measurableSet_le M.measurable_V measurable_const),
    hm.setIntegral_le hU hg]

/-- The probability of treatment: under uniform resistance, instrument independence and
thresholds in the unit interval, `P(D = 1) = ∫ p d(law of Z) = E[p(Z)]`. -/
theorem measureReal_treated [IsProbabilityMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) (hp : ∀ z, M.p z ∈ Icc (0 : ℝ) 1) :
    μ.real {ω | M.D ω = true} = ∫ z, M.p z ∂(μ.map M.Z) := by
  set F : 𝒵 × (ℝ × ℝ × ℝ) → ℝ := fun x ↦ if x.2.2.2 ≤ M.p x.1 then 1 else 0 with hF
  have hFm : Measurable F :=
    Measurable.ite (measurableSet_le (measurable_snd.comp (measurable_snd.comp measurable_snd))
      (M.measurable_p.comp measurable_fst)) measurable_const measurable_const
  have hb : ∀ z w, ‖F (z, w)‖ ≤ (fun _ : ℝ × ℝ × ℝ ↦ (1 : ℝ)) w := by
    intro z w; simp only [hF]; split_ifs <;> simp
  have key := hI.integral_eq hFm measurable_const (integrable_const _) hb
  have hL : (fun ω ↦ F (M.Z ω, M.latent ω)) = {ω | M.D ω = true}.indicator 1 := by
    funext ω; simp [hF, Set.indicator, latent, D]
  rw [← integral_indicator_one M.measurableSet_D, ← hL, key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  have e : (fun ω ↦ F (z, M.latent ω)) = {ω | M.V ω ≤ M.p z}.indicator 1 := by
    funext ω; simp [hF, latent, Set.indicator]
  simp only [e]
  rw [integral_indicator_one (measurableSet_le M.measurable_V measurable_const),
    hU.measureReal_le (hp z)]

/-! ### Local instrumental variables -/

variable (M) in
/-- The mean outcome curve `q ↦ E[Y₀] + ∫₀^q MTE(v) dv`. -/
noncomputable def outcomeCurve (μ : Measure Ω) (m : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ ω, M.Y₀ ω ∂μ + mteIntegral m q

theorem continuous_mteIntegral {m : ℝ → ℝ} (hm : Integrable ((Ioc 0 1).indicator m)) :
    Continuous (mteIntegral m) :=
  intervalIntegral.continuous_primitive (fun _ _ ↦ hm.intervalIntegrable) 0

theorem norm_mteIntegral_le {m : ℝ → ℝ} (hm : Integrable ((Ioc 0 1).indicator m)) (q : ℝ) :
    ‖mteIntegral m q‖ ≤ ∫ v, ‖(Ioc 0 1).indicator m v‖ := by
  rw [mteIntegral_eq, ← integral_indicator (measurableSet_Iic.inter measurableSet_Ioc)]
  refine norm_integral_le_of_norm_le hm.norm (Filter.Eventually.of_forall fun v ↦ ?_)
  by_cases h : v ∈ Iic q ∩ Ioc 0 1
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h.2]
  · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _

/-- **Local instrumental variables, integral form.** Under uniform resistance, instrument
independence and integrable potential outcomes, the curve `q ↦ E[Y₀] + ∫₀^q MTE` is a version
of the conditional expectation of the outcome given the selection threshold `p(Z)`:
`E[Y | p(Z)] = E[Y₀] + ∫₀^{p(Z)} MTE(v) dv` almost surely. No regularity of the MTE is needed.
The value at a threshold `q` with `P(p(Z) = q) > 0` is the elementary conditional mean, by
`LatentIndexModel.condMean_Y` with `S = p⁻¹ {q}`. -/
theorem IsMTE.condExp_Y [IsProbabilityMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) {m : ℝ → ℝ} (hm : M.IsMTE μ m)
    (h₀ : Integrable M.Y₀ μ) (h₁ : Integrable M.Y₁ μ) :
    μ[M.Y | MeasurableSpace.comap (M.p ∘ M.Z) inferInstance] =ᵐ[μ]
      fun ω ↦ M.outcomeCurve μ m (M.p (M.Z ω)) := by
  have hPZ : Measurable (M.p ∘ M.Z) := M.measurable_p.comp M.measurable_Z
  have hint := hm.integrable_indicator hU
  have hL : Continuous (M.outcomeCurve μ m) :=
    continuous_const.add (continuous_mteIntegral hint)
  have hYi : Integrable M.Y μ := by
    refine Integrable.mono' (h₀.norm.add h₁.norm) M.measurable_Y.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp only [Y]
    split_ifs
    · exact le_add_of_nonneg_left (norm_nonneg _)
    · exact le_add_of_nonneg_right (norm_nonneg _)
  have hgi : Integrable (fun ω ↦ M.outcomeCurve μ m (M.p (M.Z ω))) μ := by
    refine Integrable.of_bound (hL.measurable.comp hPZ).aestronglyMeasurable
      (‖∫ ω, M.Y₀ ω ∂μ‖ + ∫ v, ‖(Ioc 0 1).indicator m v‖)
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_mteIntegral_le hint _))
  refine (ae_eq_condExp_of_forall_setIntegral_eq hPZ.comap_le hYi
    (fun _ _ _ ↦ hgi.integrableOn) ?_
    ((hL.measurable.comp (comap_measurable (M.p ∘ M.Z))).aestronglyMeasurable)).symm
  rintro _ ⟨B, hB, rfl⟩ _
  have hS : MeasurableSet (M.p ⁻¹' B) := M.measurable_p hB
  have e : (M.p ∘ M.Z) ⁻¹' B = M.Z ⁻¹' (M.p ⁻¹' B) := rfl
  rw [e, ← integral_indicator (M.measurable_Z hS), ← integral_indicator (M.measurable_Z hS),
    hm.integral_indicator_Y hU hI h₀ h₁ hS]
  have e2 : (M.Z ⁻¹' (M.p ⁻¹' B)).indicator (fun ω ↦ M.outcomeCurve μ m (M.p (M.Z ω))) =
      fun ω ↦ (M.p ⁻¹' B).indicator (fun z ↦ M.outcomeCurve μ m (M.p z)) (M.Z ω) := by
    funext ω
    by_cases h : M.Z ω ∈ M.p ⁻¹' B
    · rw [Set.indicator_of_mem (show ω ∈ M.Z ⁻¹' (M.p ⁻¹' B) from h), Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (show ω ∉ M.Z ⁻¹' (M.p ⁻¹' B) from h),
        Set.indicator_of_notMem h]
  rw [e2]
  exact (integral_map M.measurable_Z.aemeasurable
    ((hL.measurable.comp M.measurable_p).indicator hS).aestronglyMeasurable).symm

/-- **Local instrumental variables, derivative form** (Heckman and Vytlacil, 1999, *Local
instrumental variables and latent variable models for identifying and bounding treatment
effects*). For a threshold `q` in the open unit interval at which the chosen version `m` of the
MTE is continuous, the mean outcome curve `q ↦ E[Y₀] + ∫₀^q MTE` of
`LatentIndexModel.IsMTE.condExp_Y` has derivative `m q` at `q`. The curve does not depend on the
version of the MTE; the derivative statement concerns the version `m`. -/
theorem IsMTE.hasDerivAt_outcomeCurve (hU : M.UniformResistance μ) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) (hc : ContinuousAt m q) :
    HasDerivAt (M.outcomeCurve μ m) (m q) q := by
  have hint := hm.integrable_indicator hU
  have hcont : ContinuousAt ((Ioc 0 1).indicator m) q := by
    refine hc.congr ?_
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with v hv
    rw [Set.indicator_of_mem (Ioo_subset_Ioc_self hv)]
  have h := intervalIntegral.integral_hasDerivAt_right (a := 0) hint.intervalIntegrable
    (hm.1.indicator measurableSet_Ioc).aestronglyMeasurable.stronglyMeasurableAtFilter hcont
  rw [Set.indicator_of_mem (Ioo_subset_Ioc_self hq)] at h
  exact h.const_add _

/-! ### Treatment parameters as weighted averages of the MTE -/

variable (M) in
/-- The average treatment effect on the treated, `E[Y₁ - Y₀ | D = 1]`. -/
noncomputable def att (μ : Measure Ω) : ℝ := ∫ ω, M.gain ω ∂μ[|{ω | M.D ω = true}]

variable (M) in
/-- The average treatment effect on the untreated, `E[Y₁ - Y₀ | D = 0]`. -/
noncomputable def atu (μ : Measure Ω) : ℝ := ∫ ω, M.gain ω ∂μ[|{ω | M.D ω = false}]

variable (M) in
/-- The weight of the effect on the treated at resistance `v`:
`P(p(Z) ≥ v) / P(D = 1)`. -/
noncomputable def attWeight (μ : Measure Ω) (v : ℝ) : ℝ :=
  μ.real {ω | v ≤ M.p (M.Z ω)} / μ.real {ω | M.D ω = true}

variable (M) in
/-- The weight of the effect on the untreated at resistance `v`:
`P(p(Z) < v) / P(D = 0)`. -/
noncomputable def atuWeight (μ : Measure Ω) (v : ℝ) : ℝ :=
  μ.real {ω | M.p (M.Z ω) < v} / μ.real {ω | M.D ω = false}

/-- The probability `P(p(Z) ≥ v)` as a function of `v` is measurable (it is antitone). -/
theorem measurable_measureReal_le [IsFiniteMeasure μ] :
    Measurable fun v : ℝ ↦ μ.real {ω | v ≤ M.p (M.Z ω)} :=
  Antitone.measurable fun _ _ hab ↦ measureReal_mono fun _ h ↦ le_trans hab h

theorem measureReal_le_eq_map (v : ℝ) :
    (μ.map M.Z).real {z | v ≤ M.p z} = μ.real {ω | v ≤ M.p (M.Z ω)} :=
  map_measureReal_apply M.measurable_Z (measurableSet_le measurable_const M.measurable_p)

/-- `E[(Y₁ - Y₀) 1{D = 1}] = ∫_{(0, 1]} P(p(Z) ≥ v) MTE(v) dv`. -/
theorem IsMTE.integral_indicator_treated_gain_eq [IsProbabilityMeasure μ]
    (hU : M.UniformResistance μ) (hI : M.InstrumentIndependence μ) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m) (hg : Integrable M.gain μ) :
    ∫ ω, {ω | M.D ω = true}.indicator M.gain ω ∂μ =
      ∫ v in Ioc 0 1, μ.real {ω | v ≤ M.p (M.Z ω)} * m v := by
  rw [hm.integral_indicator_treated_gain hU hI hg,
    integral_mteIntegral_comp M.measurable_p hm.1 (hm.integrableOn hU)]
  simp_rw [measureReal_le_eq_map]

/-- **The effect on the treated as a weighted average of the MTE.** Under uniform resistance,
instrument independence, an integrable gain and `P(D = 1) ≠ 0`:
`ATT = ∫₀¹ MTE(v) P(p(Z) ≥ v) / P(D = 1) dv`. -/
theorem IsMTE.att_eq [IsProbabilityMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) {m : ℝ → ℝ} (hm : M.IsMTE μ m)
    (hg : Integrable M.gain μ) (_hD : μ {ω | M.D ω = true} ≠ 0) :
    M.att μ = ∫ v in Ioc 0 1, m v * M.attWeight μ v := by
  rw [att, IVModel.integral_cond_eq_inv_mul, ← integral_indicator M.measurableSet_D,
    hm.integral_indicator_treated_gain_eq hU hI hg, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
  simp only [attWeight]
  ring

/-- `∫₀¹ P(p(Z) ≥ v) dv = P(D = 1)` for thresholds in the unit interval. -/
theorem integral_measureReal_le [IsProbabilityMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) (hp : ∀ z, M.p z ∈ Icc (0 : ℝ) 1) :
    ∫ v in Ioc 0 1, μ.real {ω | v ≤ M.p (M.Z ω)} = μ.real {ω | M.D ω = true} := by
  have h1 : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioc 0 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have key := integral_mteIntegral_comp (ν := μ.map M.Z) M.measurable_p measurable_const h1
  have e : ∀ z, mteIntegral (fun _ ↦ (1 : ℝ)) (M.p z) = M.p z := by
    intro z
    have h := mteIntegral_sub (h1.integrable_indicator measurableSet_Ioc) le_rfl (hp z).1 (hp z).2
    have h0 : mteIntegral (fun _ ↦ (1 : ℝ)) 0 = 0 := intervalIntegral.integral_same
    rw [h0, sub_zero] at h
    rw [h, setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc,
      sub_zero, max_eq_left (hp z).1]
  simp_rw [e, mul_one, measureReal_le_eq_map] at key
  rw [← key, measureReal_treated hU hI hp]

/-- **The weights of the effect on the treated integrate to one**:
`∫₀¹ P(p(Z) ≥ v) / P(D = 1) dv = 1`, for thresholds in the unit interval and `P(D = 1) ≠ 0`. -/
theorem integral_attWeight [IsProbabilityMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) (hp : ∀ z, M.p z ∈ Icc (0 : ℝ) 1)
    (hD : μ {ω | M.D ω = true} ≠ 0) :
    ∫ v in Ioc 0 1, M.attWeight μ v = 1 := by
  simp only [attWeight]
  rw [integral_div, integral_measureReal_le hU hI hp]
  exact div_self (ENNReal.toReal_ne_zero.2 ⟨hD, measure_ne_top _ _⟩)

theorem setOf_D_false : {ω | M.D ω = false} = {ω | M.D ω = true}ᶜ := by
  ext ω; simp

theorem setOf_lt_eq_compl (v : ℝ) :
    {ω | M.p (M.Z ω) < v} = {ω | v ≤ M.p (M.Z ω)}ᶜ := by
  ext ω; simp

/-- `E[(Y₁ - Y₀) 1{D = 0}] = ∫_{(0, 1]} P(p(Z) < v) MTE(v) dv`. -/
theorem IsMTE.setIntegral_untreated_gain_eq [IsProbabilityMeasure μ]
    (hU : M.UniformResistance μ) (hI : M.InstrumentIndependence μ) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m) (hg : Integrable M.gain μ) :
    ∫ ω in {ω | M.D ω = false}, M.gain ω ∂μ =
      ∫ v in Ioc 0 1, μ.real {ω | M.p (M.Z ω) < v} * m v := by
  have hmi := hm.integrableOn hU
  have hPm : IntegrableOn (fun v ↦ μ.real {ω | v ≤ M.p (M.Z ω)} * m v) (Ioc 0 1) := by
    refine Integrable.mono' hmi.norm (measurable_measureReal_le.mul hm.1).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v ↦ ?_)
    rw [norm_mul, Real.norm_of_nonneg measureReal_nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) measureReal_le_one
  have h := integral_add_compl M.measurableSet_D hg
  rw [← integral_indicator M.measurableSet_D, hm.integral_indicator_treated_gain_eq hU hI hg,
    hm.integral_gain hU hg] at h
  rw [setOf_D_false, eq_sub_of_add_eq' h, ← integral_sub hmi hPm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
  simp only
  rw [setOf_lt_eq_compl, probReal_compl_eq_one_sub
    (show MeasurableSet {ω | v ≤ M.p (M.Z ω)} from
        measurableSet_le measurable_const (M.measurable_p.comp M.measurable_Z))]
  ring

/-- **The effect on the untreated as a weighted average of the MTE.** Under uniform
resistance, instrument independence, an integrable gain and `P(D = 0) ≠ 0`:
`ATU = ∫₀¹ MTE(v) P(p(Z) < v) / P(D = 0) dv`. -/
theorem IsMTE.atu_eq [IsProbabilityMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) {m : ℝ → ℝ} (hm : M.IsMTE μ m)
    (hg : Integrable M.gain μ) (_hD : μ {ω | M.D ω = false} ≠ 0) :
    M.atu μ = ∫ v in Ioc 0 1, m v * M.atuWeight μ v := by
  rw [atu, IVModel.integral_cond_eq_inv_mul, hm.setIntegral_untreated_gain_eq hU hI hg,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
  simp only [atuWeight]
  ring

/-- **The weights of the effect on the untreated integrate to one**:
`∫₀¹ P(p(Z) < v) / P(D = 0) dv = 1`, for thresholds in the unit interval and `P(D = 0) ≠ 0`. -/
theorem integral_atuWeight [IsProbabilityMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) (hp : ∀ z, M.p z ∈ Icc (0 : ℝ) 1)
    (hD : μ {ω | M.D ω = false} ≠ 0) :
    ∫ v in Ioc 0 1, M.atuWeight μ v = 1 := by
  have hP : IntegrableOn (fun v ↦ μ.real {ω | v ≤ M.p (M.Z ω)}) (Ioc 0 1) := by
    refine Integrable.mono' (integrableOn_const measure_Ioc_lt_top.ne (C := (1 : ℝ)))
      measurable_measureReal_le.aestronglyMeasurable (Filter.Eventually.of_forall fun v ↦ ?_)
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have e : ∫ v in Ioc 0 1, μ.real {ω | M.p (M.Z ω) < v} = μ.real {ω | M.D ω = false} := by
    have e1 : (fun v ↦ μ.real {ω | M.p (M.Z ω) < v}) =
        fun v ↦ 1 - μ.real {ω | v ≤ M.p (M.Z ω)} := by
      funext v
      rw [setOf_lt_eq_compl, probReal_compl_eq_one_sub
        (show MeasurableSet {ω | v ≤ M.p (M.Z ω)} from
        measurableSet_le measurable_const (M.measurable_p.comp M.measurable_Z))]
    rw [e1, integral_sub (integrableOn_const measure_Ioc_lt_top.ne) hP,
      integral_measureReal_le hU hI hp, setIntegral_const, smul_eq_mul, mul_one,
      Real.volume_real_Ioc, sub_zero, max_eq_left zero_le_one, setOf_D_false,
      probReal_compl_eq_one_sub M.measurableSet_D]
  simp only [atuWeight]
  rw [integral_div, e]
  exact div_self (ENNReal.toReal_ne_zero.2 ⟨hD, measure_ne_top _ _⟩)

/-- The weight of the band `(q, q']` at resistance `v`: `1{q < v ≤ q'} / (q' - q)`. -/
noncomputable def lateWeight (q q' v : ℝ) : ℝ := (Ioc q q').indicator (fun _ ↦ (q' - q)⁻¹) v

/-- **The LATE of a band as a weighted average of the MTE**, with weight
`1{q < v ≤ q'} / (q' - q)`, for `0 ≤ q < q' ≤ 1`. -/
theorem IsMTE.lateBetween_eq_weighted [IsFiniteMeasure μ] (hU : M.UniformResistance μ)
    {m : ℝ → ℝ} (hm : M.IsMTE μ m) (hint : Integrable M.gain μ) {q q' : ℝ} (hq : 0 ≤ q)
    (hqq : q < q') (hq' : q' ≤ 1) :
    M.lateBetween μ q q' = ∫ v in Ioc 0 1, m v * lateWeight q q' v := by
  have hsub : Ioc q q' ⊆ Ioc (0 : ℝ) 1 := fun v hv ↦ ⟨hq.trans_lt hv.1, hv.2.trans hq'⟩
  have e : (fun v ↦ m v * lateWeight q q' v) = (Ioc q q').indicator fun v ↦ m v * (q' - q)⁻¹ := by
    funext v
    by_cases h : v ∈ Ioc q q'
    · simp [lateWeight, Set.indicator_of_mem h]
    · simp [lateWeight, Set.indicator_of_notMem h]
  rw [hm.lateBetween_eq hU hint hq hqq hq', e, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.2 hsub, integral_mul_const, div_eq_mul_inv]

/-- **The average treatment effect has weight one**: `ATE = ∫₀¹ MTE(v) · 1 dv`. -/
theorem IsMTE.ate_eq_weighted [IsFiniteMeasure μ] (hU : M.UniformResistance μ) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m) (hint : Integrable M.gain μ) :
    ∫ ω, M.gain ω ∂μ = ∫ v in Ioc 0 1, m v * 1 := by
  simp_rw [mul_one]
  exact hm.integral_gain hU hint

/-- **A constant MTE collapses the treatment parameters.** If the MTE equals `β` almost
everywhere on the unit interval, then the average treatment effect, the effect on the treated,
the effect on the untreated and every band LATE equal `β`. A constant MTE does not require a
constant unit-level gain: only its mean given the resistance is constant. -/
theorem IsMTE.collapse_of_const [IsProbabilityMeasure μ] (hU : M.UniformResistance μ)
    (hI : M.InstrumentIndependence μ) (hp : ∀ z, M.p z ∈ Icc (0 : ℝ) 1) {m : ℝ → ℝ}
    (hm : M.IsMTE μ m) (hg : Integrable M.gain μ) {β : ℝ}
    (hβ : ∀ᵐ v ∂(volume.restrict (Ioc 0 1)), m v = β)
    (hD₁ : μ {ω | M.D ω = true} ≠ 0) (hD₀ : μ {ω | M.D ω = false} ≠ 0) :
    ∫ ω, M.gain ω ∂μ = β ∧ M.att μ = β ∧ M.atu μ = β ∧
      ∀ q q', 0 ≤ q → q < q' → q' ≤ 1 → M.lateBetween μ q q' = β := by
  have avg : ∀ w : ℝ → ℝ, ∫ v in Ioc 0 1, w v = 1 → ∫ v in Ioc 0 1, m v * w v = β := by
    intro w hw
    rw [integral_congr_ae (hβ.mono fun v h ↦ by rw [h]), integral_const_mul, hw, mul_one]
  refine ⟨?_, ?_, ?_, fun q q' hq hqq hq' ↦ ?_⟩
  · rw [hm.ate_eq_weighted hU hg, avg _ ?_]
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc, sub_zero,
      max_eq_left zero_le_one]
  · rw [hm.att_eq hU hI hg hD₁, avg _ (integral_attWeight hU hI hp hD₁)]
  · rw [hm.atu_eq hU hI hg hD₀, avg _ (integral_atuWeight hU hI hp hD₀)]
  · have hsub : Ioc q q' ⊆ Ioc (0 : ℝ) 1 := fun v hv ↦ ⟨hq.trans_lt hv.1, hv.2.trans hq'⟩
    rw [hm.lateBetween_eq_weighted hU hg hq hqq hq', avg]
    unfold lateWeight
    rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul,
      measureReal_restrict_apply measurableSet_Ioc, inter_eq_left.2 hsub, Real.volume_real_Ioc,
      max_eq_left (by linarith)]
    exact mul_inv_cancel₀ (by linarith)

/-! ### The link with the binary instrument model and the LATE theorem -/

/-- A latent index model with a binary instrument, seen as a binary instrumental variable model
(`CausalInference.IVModel`): the potential treatment at instrument value `b` is
`1{V ≤ p b}` and the potential outcome under treatment `d` is `Y_d`, whatever the instrument. -/
noncomputable def toIVModel (M : LatentIndexModel Ω Bool) : IVModel Ω where
  Z := M.Z
  D b ω := decide (M.V ω ≤ M.p b)
  Y _ d ω := if d then M.Y₁ ω else M.Y₀ ω
  measurable_Z := M.measurable_Z
  measurable_D b := measurable_to_countable' fun c ↦ by
    cases c
    · have : (fun ω ↦ decide (M.V ω ≤ M.p b)) ⁻¹' {false} = {ω | M.V ω ≤ M.p b}ᶜ := by
        ext ω; simp
      rw [this]; exact (measurableSet_le M.measurable_V measurable_const).compl
    · have : (fun ω ↦ decide (M.V ω ≤ M.p b)) ⁻¹' {true} = {ω | M.V ω ≤ M.p b} := by
        ext ω; simp
      rw [this]; exact measurableSet_le M.measurable_V measurable_const
  measurable_Y _ d := by cases d <;> simp [M.measurable_Y₀, M.measurable_Y₁]

section Binary

variable {B : LatentIndexModel Ω Bool}

theorem toIVModel_Dobs : B.toIVModel.Dobs = B.D := rfl

theorem toIVModel_Yobs : B.toIVModel.Yobs = B.Y := rfl

theorem toIVModel_effect (b : Bool) : B.toIVModel.effect b = B.gain := rfl

theorem toIVModel_condMean (f : Ω → ℝ) (b : Bool) :
    B.toIVModel.condMean μ f b = B.condMean μ f {b} := rfl

/-- The compliers of the binary model are the units with resistance in `(p false, p true]`. -/
theorem toIVModel_compliers : B.toIVModel.compliers = B.V ⁻¹' Ioc (B.p false) (B.p true) := by
  ext ω
  rw [IVModel.mem_compliers]
  exact decide_le_iff (M := B) (z := false) (z' := true)

/-- **The index structure implies the monotonicity of the LATE theorem**: if
`p false ≤ p true`, the binary model satisfies `IVModel.Monotonicity` (indeed everywhere). -/
theorem toIVModel_monotonicity (h : B.p false ≤ B.p true) : B.toIVModel.Monotonicity μ :=
  Filter.Eventually.of_forall fun ω ↦ decide_le_mono (M := B) h ω

theorem toIVModel_exclusion : B.toIVModel.Exclusion μ := fun _ ↦ Filter.EventuallyEq.rfl

/-- Independence of the instrument from the latent vector gives the instrument independence of
the binary model: its potential variables are a measurable function of `(Y₀, Y₁, V)`. -/
theorem toIVModel_independence (hI : B.InstrumentIndependence μ) :
    B.toIVModel.InstrumentIndependence μ := by
  set ψ : ℝ × ℝ × ℝ → IVModel.Potentials := fun w ↦
    (fun b ↦ decide (w.2.2 ≤ B.p b), fun _ d ↦ if d then w.2.1 else w.1) with hψ
  have hψm : Measurable ψ := by
    refine Measurable.prodMk (Measurable.of_eval fun b ↦ ?_)
      (Measurable.of_eval fun _ ↦ Measurable.of_eval fun d ↦ ?_)
    · exact measurable_to_countable' fun c ↦ by
        cases c
        · have : (fun w : ℝ × ℝ × ℝ ↦ decide (w.2.2 ≤ B.p b)) ⁻¹' {false} =
              {w | w.2.2 ≤ B.p b}ᶜ := by ext w; simp
          rw [this]
          exact (measurableSet_le (measurable_snd.comp measurable_snd) measurable_const).compl
        · have : (fun w : ℝ × ℝ × ℝ ↦ decide (w.2.2 ≤ B.p b)) ⁻¹' {true} =
              {w | w.2.2 ≤ B.p b} := by ext w; simp
          rw [this]
          exact measurableSet_le (measurable_snd.comp measurable_snd) measurable_const
    · cases d
      · exact measurable_fst
      · exact measurable_fst.comp measurable_snd
  have h := hI.comp measurable_id hψm
  have e : B.toIVModel.potentials = ψ ∘ B.latent := by
    funext ω; rfl
  rw [IVModel.InstrumentIndependence, e]
  exact h

/-- **The latent index model satisfies the hypotheses of the LATE theorem**: under uniform
resistance, instrument independence, integrable potential outcomes, both instrument arms of
positive probability, and `0 ≤ p false < p true ≤ 1`, the binary model satisfies
`IVModel.LATEAssumptions`. -/
theorem toIVModel_lateAssumptions [IsFiniteMeasure μ] (hU : B.UniformResistance μ)
    (hI : B.InstrumentIndependence μ) (h₀ : Integrable B.Y₀ μ) (h₁ : Integrable B.Y₁ μ)
    (hf : μ (B.Z ⁻¹' {false}) ≠ 0) (ht : μ (B.Z ⁻¹' {true}) ≠ 0) (hp : 0 ≤ B.p false)
    (hpp : B.p false < B.p true) (hp' : B.p true ≤ 1) :
    B.toIVModel.LATEAssumptions μ where
  exclusion := toIVModel_exclusion
  independence := toIVModel_independence hI
  monotonicity := toIVModel_monotonicity hpp.le
  relevance := by
    refine ⟨ht, hf, ?_⟩
    rw [IVModel.firstStage, toIVModel_condMean, toIVModel_condMean]
    change B.condMean μ B.DReal {true} - B.condMean μ B.DReal {false} ≠ 0
    rw [B.condMean_DReal hU hI (measurableSet_singleton true) ht ⟨hp.trans hpp.le, hp'⟩
        (fun _ h ↦ by rw [h]),
      B.condMean_DReal hU hI (measurableSet_singleton false) hf ⟨hp, hpp.le.trans hp'⟩
        (fun _ h ↦ by rw [h])]
    exact sub_ne_zero.2 hpp.ne'
  integrable z := B.toIVModel.integrable_Y_D (fun d ↦ by cases d <;> assumption) z

/-- **The link with the LATE theorem.** In the binary case, the Wald ratio of the binary model
(`IVModel.wald`) equals the complier average causal effect by the LATE theorem
(`IVModel.LATEAssumptions.wald_eq`), the compliers are the units with resistance in
`(p false, p true]`, and both equal the average MTE over that band. -/
theorem IsMTE.toIVModel_wald_eq [IsProbabilityMeasure μ] (hU : B.UniformResistance μ)
    (hI : B.InstrumentIndependence μ) {m : ℝ → ℝ} (hm : B.IsMTE μ m)
    (h₀ : Integrable B.Y₀ μ) (h₁ : Integrable B.Y₁ μ)
    (hf : μ (B.Z ⁻¹' {false}) ≠ 0) (ht : μ (B.Z ⁻¹' {true}) ≠ 0) (hp : 0 ≤ B.p false)
    (hpp : B.p false < B.p true) (hp' : B.p true ≤ 1) (z : Bool) :
    B.toIVModel.wald μ = B.toIVModel.complierEffect μ z ∧
      B.toIVModel.complierEffect μ z = B.lateBetween μ (B.p false) (B.p true) ∧
      B.toIVModel.wald μ = (∫ v in Ioc (B.p false) (B.p true), m v) / (B.p true - B.p false) := by
  have hL := toIVModel_lateAssumptions hU hI h₀ h₁ hf ht hp hpp hp'
  have hC : B.toIVModel.complierEffect μ z = B.lateBetween μ (B.p false) (B.p true) := by
    rw [IVModel.complierEffect, toIVModel_compliers, toIVModel_effect, lateBetween]
  refine ⟨hL.wald_eq z, hC, ?_⟩
  rw [hL.wald_eq z, hC, hm.lateBetween_eq hU (h₁.sub h₀) hp hpp hp']

/-- In the binary case the effect on the treated of the latent index model is the effect on the
treated `IVModel.att` of the binary model. -/
theorem toIVModel_att (z : Bool) : B.toIVModel.att μ z = B.att μ := rfl

end Binary

end LatentIndexModel

namespace IVModel

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A binary instrument model **has a latent index representation** if its potential treatments
are thresholds of one latent variable: `D b ω = 1{V ω ≤ p b}` for some `V` and some thresholds
`p false`, `p true`. -/
def HasLatentIndex (M : IVModel Ω) : Prop :=
  ∃ (V : Ω → ℝ) (p : Bool → ℝ), ∀ b ω, M.D b ω = decide (V ω ≤ p b)

/-- **A latent index representation forces one-way flows**: either every unit treated at
`false` is treated at `true`, or every unit treated at `true` is treated at `false`. -/
theorem HasLatentIndex.monotone {M : IVModel Ω} (h : M.HasLatentIndex) :
    (∀ ω, M.D false ω ≤ M.D true ω) ∨ (∀ ω, M.D true ω ≤ M.D false ω) := by
  obtain ⟨V, p, hVp⟩ := h
  rcases le_total (p false) (p true) with hp | hp
  · refine Or.inl fun ω ↦ ?_
    rw [hVp, hVp]
    by_cases h1 : V ω ≤ p false
    · simp [h1, h1.trans hp]
    · simp [h1]
  · refine Or.inr fun ω ↦ ?_
    rw [hVp, hVp]
    by_cases h1 : V ω ≤ p true
    · simp [h1, h1.trans hp]
    · simp [h1]

end IVModel

namespace IVCounterexample

open IVModel

/-- **Two-way flows: the defier countermodel has no latent index representation.** In
`IVCounterexample.modelA` units `0` and `1` are compliers and unit `2` is a defier, so no single
latent resistance with instrument-dependent thresholds generates its treatments. -/
theorem modelA_not_hasLatentIndex : ¬ modelA.HasLatentIndex := by
  intro h
  rcases h.monotone with h' | h'
  · have := h' ((true, 2) : Space 3)
    revert this
    simp only [modelA]
    decide
  · have := h' ((true, 0) : Space 3)
    revert this
    simp only [modelA]
    decide

/-- **Without the index structure the Wald ratio is not a nonnegative average of effects.** In
`IVCounterexample.modelA` every unit-level effect is `1` or `4`, hence at least `1`, while the
Wald ratio is `-2`: for every nonnegative weighting `w` of the six points of the sample space
with total weight `1`, the Wald ratio differs from `∑ w ω (Y₁ - Y₀)(ω)`. In a latent index model
the Wald ratio is the average of the MTE over a band (`LatentIndexModel.IsMTE.wald_eq`), an
average with nonnegative weights. -/
theorem modelA_wald_ne_weighted (w : Space 3 → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1) :
    modelA.wald (P 3) ≠ ∑ ω, w ω * modelA.effect true ω := by
  have hge : ∀ ω : Space 3, 1 ≤ modelA.effect true ω := by
    rintro ⟨b, u⟩
    fin_cases u <;> norm_num [IVModel.effect, modelA]
  have h1 : 1 ≤ ∑ ω, w ω * modelA.effect true ω := by
    calc (1 : ℝ) = ∑ ω, w ω * 1 := by simp [hsum]
      _ ≤ ∑ ω, w ω * modelA.effect true ω :=
        Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hge ω) (hw ω)
  rw [modelA_wald]
  intro h
  linarith

end IVCounterexample

end CausalInference
