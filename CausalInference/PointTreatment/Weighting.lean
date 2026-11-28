/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Identification
public import Mathlib.Probability.Moments.Variance

/-!
# Point treatment: inverse probability weighting

The inverse probability weight of the arm `a` is `w_a = 1{A = a} / π_a(W)`, with
`π_a = armProb e a` built from a score `e` of the treated arm. The Horvitz and Thompson form of
the weighted arm mean is `E[w_a Y]`; the Hájek form divides it by `E[w_a]`.

At the true propensity score the weights have mean one, so both forms equal `E[Y(a)]`. Under
ignorability their second moments are exact: `E[w_a²] = E[1 / π_a(W)]` and
`E[(w_a Y)²] = E[Y(a)² / π_a(W)]`, each side integrable exactly when the other is. This gives
the variance of the weighted outcome and the effective sample size fraction
`E[w_a]² / E[w_a²] = 1 / E[1 / π_a(W)] ≤ 1`. Under a wrong score `ê` the bias of the
Horvitz and Thompson form is `E[(π_a(W) / π̂_a(W) - 1) E[Y(a) | W]]`.

## Main definitions

* `ipwWeight A W e a`: the weight `1{A = a} / π_a(W)`.
* `ipwTerm A Y W e a`: the weighted outcome `1{A = a} Y / π_a(W)`.
* `ipwArmMean`, `ipwAte`: the Horvitz and Thompson forms; `hajekArmMean`, `hajekAte`: the Hájek
  forms.
* `essFraction μ w`: the effective sample size fraction `E[w]² / E[w²]`.

## Main results

* `ipwWeight_integral`: at the true score the weights have mean one.
* `Ignorable.ipwArmMean_eq`, `Ignorable.ipwAte_eq`, `Ignorable.hajekArmMean_eq`,
  `Ignorable.hajekAte_eq`: unbiasedness at the true score.
* `integrable_ipwWeight_sq_iff`, `integral_ipwWeight_sq`: `E[w_a²] = E[1 / π_a(W)]`.
* `IndicatorIgnorable.integrable_ipwTerm_sq_iff`, `IndicatorIgnorable.integral_ipwTerm_sq`:
  `E[(w_a Y)²] = E[Y(a)² / π_a(W)]`.
* `IndicatorIgnorable.variance_ipwTerm`: `Var(w_a Y) = E[Y(a)² / π_a(W)] - E[Y(a)]²`.
* `variance_ipwWeight`, `essFraction_ipwWeight`, `essFraction_ipwWeight_le_one`: the variance of
  the weights and the effective sample size fraction.
* `IndicatorIgnorable.ipwArmMean_sub_armMean`: the bias under a wrong score.

## References

* D. G. Horvitz and D. J. Thompson, *A generalization of sampling without replacement from a
  finite universe*, Journal of the American Statistical Association 47 (1952).
* J. Hájek, comment on a paper by D. Basu, in *Foundations of Statistical Inference*, Holt,
  Rinehart and Winston (1971).
* L. Kish, *Survey Sampling*, Wiley (1965) (the effective sample size).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲] {μ : Measure Ω}
  {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {e : 𝒲 → ℝ}

/-! ### Definitions -/

section Definitions

omit [MeasurableSpace 𝒲]

/-- The inverse probability weight `1{A = a} / π_a(W)` of the arm `a`. -/
noncomputable def ipwWeight (A : Ω → Bool) (W : Ω → 𝒲) (e : 𝒲 → ℝ) (a : Bool) : Ω → ℝ :=
  fun ω => respInd (arm A a) ω / armProb e a (W ω)

/-- The inverse probability weighted outcome `1{A = a} Y / π_a(W)`. -/
noncomputable def ipwTerm (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲) (e : 𝒲 → ℝ)
    (a : Bool) : Ω → ℝ :=
  fun ω => respInd (arm A a) ω * obsOutcome A Y ω / armProb e a (W ω)

/-- The Horvitz and Thompson form of the arm mean, `E[1{A = a} Y / π_a(W)]`. -/
noncomputable def ipwArmMean (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲)
    (e : 𝒲 → ℝ) (a : Bool) : ℝ :=
  ∫ ω, ipwTerm A Y W e a ω ∂μ

/-- The Horvitz and Thompson form of the average effect. -/
noncomputable def ipwAte (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲)
    (e : 𝒲 → ℝ) : ℝ :=
  ipwArmMean μ A Y W e true - ipwArmMean μ A Y W e false

/-- The Hájek form of the arm mean, `E[1{A = a} Y / π_a(W)] / E[1{A = a} / π_a(W)]`. -/
noncomputable def hajekArmMean (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲)
    (e : 𝒲 → ℝ) (a : Bool) : ℝ :=
  ipwArmMean μ A Y W e a / ∫ ω, ipwWeight A W e a ω ∂μ

/-- The Hájek form of the average effect. -/
noncomputable def hajekAte (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲)
    (e : 𝒲 → ℝ) : ℝ :=
  hajekArmMean μ A Y W e true - hajekArmMean μ A Y W e false

/-- The effective sample size fraction `E[w]² / E[w²]` of a weight `w` (Kish): the effective
sample size divided by the sample size. -/
noncomputable def essFraction (μ : Measure Ω) (w : Ω → ℝ) : ℝ :=
  (∫ ω, w ω ∂μ) ^ 2 / ∫ ω, w ω ^ 2 ∂μ

theorem respInd_mul_self (R : Ω → Bool) (ω : Ω) : respInd R ω * respInd R ω = respInd R ω := by
  rw [respInd_apply]; split_ifs <;> simp

end Definitions

/-! ### Weights of mean one and unbiasedness -/

theorem measurable_ipwWeight (hW : Measurable W) (hA : Measurable A) (he : Measurable e)
    (a : Bool) : Measurable (ipwWeight A W e a) :=
  (measurable_respInd (measurable_arm hA a)).div ((measurable_armProb he a).comp hW)

theorem measurable_ipwTerm (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (he : Measurable e) (a : Bool) : Measurable (ipwTerm A Y W e a) :=
  ((measurable_respInd (measurable_arm hA a)).mul (measurable_obsOutcome hA hY)).div
    ((measurable_armProb he a).comp hW)

/-- **The weights have mean one** at the true propensity score: `E[1{A = a} / π_a(W)] = 1` under
positivity of the arm. No ignorability is needed. -/
theorem ipwWeight_integral [IsProbabilityMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) :
    Integrable (ipwWeight A W e a) μ ∧ ∫ ω, ipwWeight A W e a ω ∂μ = 1 :=
  ipw_weight_integral hW (measurable_arm hA a) (measurable_armProb hps.1 a)
    (hps.condExp_arm hW hA a) hpos

/-- **Unbiasedness of the Horvitz and Thompson arm mean** at the true score under
ignorability. -/
theorem Ignorable.ipwArmMean_eq [StandardBorelSpace Ω] [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : Ignorable μ A hW Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hYi : Integrable (Y a) μ) : ipwArmMean μ A Y W e a = armMean μ Y a :=
  (hign.armMean_eq_ipw hW hA hY hps a hpos hYi).symm

/-- **Unbiasedness of the Horvitz and Thompson average effect** at the true score under
ignorability and positivity. -/
theorem Ignorable.ipwAte_eq [StandardBorelSpace Ω] [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : Ignorable μ A hW Y) (hps : IsPropensityScore μ A W e)
    (hov : OverlapAE e (μ.map W)) : ipwAte μ A Y W e = ate μ Y := by
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  rw [ipwAte, hign.ipwArmMean_eq hW hA hY hps true (hpos true) (hYi true),
    hign.ipwArmMean_eq hW hA hY hps false (hpos false) (hYi false),
    ate_eq_armMean_sub (hYi true) (hYi false)]

/-- **Unbiasedness of the Hájek arm mean** at the true score: the denominator is one. -/
theorem Ignorable.hajekArmMean_eq [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hign : Ignorable μ A hW Y) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) (hYi : Integrable (Y a) μ) :
    hajekArmMean μ A Y W e a = armMean μ Y a := by
  rw [hajekArmMean, (ipwWeight_integral hW hA hps a hpos).2, div_one,
    hign.ipwArmMean_eq hW hA hY hps a hpos hYi]

/-- **Unbiasedness of the Hájek average effect** at the true score. -/
theorem Ignorable.hajekAte_eq [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hign : Ignorable μ A hW Y)
    (hps : IsPropensityScore μ A W e) (hov : OverlapAE e (μ.map W)) :
    hajekAte μ A Y W e = ate μ Y := by
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  rw [hajekAte, hign.hajekArmMean_eq hW hA hY hps true (hpos true) (hYi true),
    hign.hajekArmMean_eq hW hA hY hps false (hpos false) (hYi false),
    ate_eq_armMean_sub (hYi true) (hYi false)]

/-! ### Second moments, variance and effective sample size -/

/-- The weighting lemma on an arm, conditioning on `W` only: for a measurable `g` of the
conditioning variable, `1{A = a} g(W)` is integrable exactly when `π_a(W) g(W)` is, and then
the two have the same mean. -/
theorem integrable_respInd_arm_mul_iff [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hps : IsPropensityScore μ A W e) (a : Bool) {g : 𝒲 → ℝ}
    (hg : Measurable g) :
    Integrable (fun ω => respInd (arm A a) ω * g (W ω)) μ ↔
      Integrable (fun ω => armProb e a (W ω) * g (W ω)) μ := by
  have hgm : StronglyMeasurable[MeasurableSpace.comap W inferInstance] (fun ω => g (W ω)) :=
    (hg.comp (comap_measurable W)).stronglyMeasurable
  have hr := integrable_respInd (μ := μ) (measurable_arm hA a)
  exact ⟨fun h => (integral_mul_eq_of_condExp_eq hW.comap_le hr hgm h
      (hps.condExp_arm hW hA a)).1,
    integrable_mul_of_condExp_eq hW.comap_le hr
      (Filter.Eventually.of_forall fun ω => respInd_nonneg _ ω) hgm (hps.condExp_arm hW hA a)⟩

/-- **Second moment of the weights.** At the true score, under positivity of the arm, the
squared weight `w_a²` is integrable exactly when `1 / π_a(W)` is. -/
theorem integrable_ipwWeight_sq_iff [IsFiniteMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) :
    Integrable (fun ω => ipwWeight A W e a ω ^ 2) μ ↔
      Integrable (fun ω => 1 / armProb e a (W ω)) μ := by
  have hsq : (fun ω => ipwWeight A W e a ω ^ 2) =
      fun ω => respInd (arm A a) ω * (1 / armProb e a (W ω) ^ 2) := by
    funext ω
    rw [ipwWeight, div_pow, sq, respInd_mul_self, mul_one_div]
  have hae : (fun ω => armProb e a (W ω) * (1 / armProb e a (W ω) ^ 2)) =ᵐ[μ]
      fun ω => 1 / armProb e a (W ω) := by
    filter_upwards [hpos] with ω hω
    field_simp
  rw [hsq, integrable_respInd_arm_mul_iff hW hA hps a
    (((measurable_armProb hps.1 a).pow_const 2).const_div 1)]
  exact integrable_congr hae

/-- **Second moment of the weights:** `E[w_a²] = E[1 / π_a(W)]` at the true score, under
positivity of the arm (both sides are integrals of integrable functions or both vanish as
integrals of non integrable ones; see `integrable_ipwWeight_sq_iff`). -/
theorem integral_ipwWeight_sq [IsFiniteMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hint : Integrable (fun ω => 1 / armProb e a (W ω)) μ) :
    ∫ ω, ipwWeight A W e a ω ^ 2 ∂μ = ∫ ω, 1 / armProb e a (W ω) ∂μ := by
  have hsq : (fun ω => ipwWeight A W e a ω ^ 2) =
      fun ω => respInd (arm A a) ω * (1 / armProb e a (W ω) ^ 2) := by
    funext ω
    rw [ipwWeight, div_pow, sq, respInd_mul_self, mul_one_div]
  have hi := (integrable_ipwWeight_sq_iff hW hA hps a hpos).2 hint
  rw [hsq] at hi ⊢
  have hgm : StronglyMeasurable[MeasurableSpace.comap W inferInstance]
      (fun ω => 1 / armProb e a (W ω) ^ 2) :=
    ((((measurable_armProb hps.1 a).pow_const 2).const_div 1).comp
      (comap_measurable W)).stronglyMeasurable
  rw [(integral_mul_eq_of_condExp_eq hW.comap_le (integrable_respInd (measurable_arm hA a))
    hgm hi (hps.condExp_arm hW hA a)).2]
  refine integral_congr_ae ?_
  filter_upwards [hpos] with ω hω
  field_simp

/-- **Variance of the weights**: `Var(w_a) = E[1 / π_a(W)] - 1` at the true score, when
`1 / π_a(W)` is integrable. -/
theorem variance_ipwWeight [IsProbabilityMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hint : Integrable (fun ω => 1 / armProb e a (W ω)) μ) :
    variance (ipwWeight A W e a) μ = ∫ ω, 1 / armProb e a (W ω) ∂μ - 1 := by
  have hm := measurable_ipwWeight hW hA hps.1 a
  have hL2 : MemLp (ipwWeight A W e a) 2 μ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
      ((integrable_ipwWeight_sq_iff hW hA hps a hpos).2 hint)
  rw [variance_eq_sub hL2]
  change ∫ ω, ipwWeight A W e a ω ^ 2 ∂μ - (∫ ω, ipwWeight A W e a ω ∂μ) ^ 2 = _
  rw [integral_ipwWeight_sq hW hA hps a hpos hint, (ipwWeight_integral hW hA hps a hpos).2]
  ring

/-- **Effective sample size of the weights**: `E[w_a]² / E[w_a²] = 1 / E[1 / π_a(W)]` at the
true score, when `1 / π_a(W)` is integrable. -/
theorem essFraction_ipwWeight [IsProbabilityMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hint : Integrable (fun ω => 1 / armProb e a (W ω)) μ) :
    essFraction μ (ipwWeight A W e a) = 1 / ∫ ω, 1 / armProb e a (W ω) ∂μ := by
  rw [essFraction, integral_ipwWeight_sq hW hA hps a hpos hint,
    (ipwWeight_integral hW hA hps a hpos).2, one_pow]

/-- `E[1 / π_a(W)] ≥ 1` at the true score, since `π_a(W) ≤ 1` almost surely. -/
theorem one_le_integral_inv_armProb [IsProbabilityMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hint : Integrable (fun ω => 1 / armProb e a (W ω)) μ) :
    1 ≤ ∫ ω, 1 / armProb e a (W ω) ∂μ := by
  have h1 : ∀ᵐ ω ∂μ, (1 : ℝ) ≤ 1 / armProb e a (W ω) := by
    filter_upwards [hps.ae_mem_Icc hW hA, hpos] with ω hω hp
    rw [le_div_iff₀ hp, one_mul]
    cases a
    · simp only [armProb_false]; linarith [hω.1]
    · exact hω.2
  calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂μ := by simp
    _ ≤ _ := integral_mono_ae (integrable_const 1) hint h1

/-- **The effective sample size fraction is at most one** at the true score. -/
theorem essFraction_ipwWeight_le_one [IsProbabilityMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hint : Integrable (fun ω => 1 / armProb e a (W ω)) μ) :
    essFraction μ (ipwWeight A W e a) ≤ 1 := by
  rw [essFraction_ipwWeight hW hA hps a hpos hint]
  have := one_le_integral_inv_armProb hW hA hps a hpos hint
  rw [div_le_one (by linarith)]
  exact this

/-- The weighting lemma on an arm, conditioning on `(W, Y(a))`: under the indicator form of
ignorability, for a measurable `g` of `(W, Y(a))`, `1{A = a} g(W, Y(a))` is integrable exactly
when `π_a(W) g(W, Y(a))` is, and then the two have the same mean. -/
theorem IndicatorIgnorable.integral_respInd_arm_mul [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) {g : 𝒲 × ℝ → ℝ} (hg : Measurable g) :
    (Integrable (fun ω => respInd (arm A a) ω * g (W ω, Y a ω)) μ ↔
      Integrable (fun ω => armProb e a (W ω) * g (W ω, Y a ω)) μ) ∧
    ∫ ω, respInd (arm A a) ω * g (W ω, Y a ω) ∂μ =
      ∫ ω, armProb e a (W ω) * g (W ω, Y a ω) ∂μ := by
  have hgm := (measurable_comap_prod (X := W) (Y := Y a) hg).stronglyMeasurable
  have hr := integrable_respInd (μ := μ) (measurable_arm hA a)
  have hp := (hign.marMean hW hA hY a).trans (hps.condExp_arm hW hA a)
  have hle := (hW.prodMk (hY a)).comap_le
  have hiff : Integrable (fun ω => respInd (arm A a) ω * g (W ω, Y a ω)) μ ↔
      Integrable (fun ω => armProb e a (W ω) * g (W ω, Y a ω)) μ :=
    ⟨fun h => (integral_mul_eq_of_condExp_eq hle hr hgm h hp).1,
      integrable_mul_of_condExp_eq hle hr
        (Filter.Eventually.of_forall fun ω => respInd_nonneg _ ω) hgm hp⟩
  refine ⟨hiff, ?_⟩
  by_cases h : Integrable (fun ω => respInd (arm A a) ω * g (W ω, Y a ω)) μ
  · exact (integral_mul_eq_of_condExp_eq hle hr hgm h hp).2
  · rw [integral_undef h, integral_undef (mt hiff.2 h)]

/-- **Second moment of the weighted outcome**, integrability: under the indicator form of
ignorability and positivity of the arm, `(w_a Y)²` is integrable exactly when
`Y(a)² / π_a(W)` is. -/
theorem IndicatorIgnorable.integrable_ipwTerm_sq_iff [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) :
    Integrable (fun ω => ipwTerm A Y W e a ω ^ 2) μ ↔
      Integrable (fun ω => Y a ω ^ 2 / armProb e a (W ω)) μ := by
  have hsq : (fun ω => ipwTerm A Y W e a ω ^ 2) =
      fun ω => respInd (arm A a) ω * (fun q : 𝒲 × ℝ => q.2 ^ 2 / armProb e a q.1 ^ 2)
        (W ω, Y a ω) := by
    funext ω
    have h1 := respInd_arm_mul_obsOutcome A Y a ω
    have h2 := respInd_mul_self (arm A a) ω
    simp only [ipwTerm]
    calc (respInd (arm A a) ω * obsOutcome A Y ω / armProb e a (W ω)) ^ 2
        = (respInd (arm A a) ω * obsOutcome A Y ω) * (respInd (arm A a) ω * obsOutcome A Y ω) /
          armProb e a (W ω) ^ 2 := by ring
      _ = (respInd (arm A a) ω * respInd (arm A a) ω) * (Y a ω ^ 2 / armProb e a (W ω) ^ 2) := by
          rw [h1]; ring
      _ = _ := by rw [h2]
  have hg : Measurable fun q : 𝒲 × ℝ => q.2 ^ 2 / armProb e a q.1 ^ 2 :=
    (measurable_snd.pow_const 2).div
      (((measurable_armProb hps.1 a).comp measurable_fst).pow_const 2)
  rw [hsq, (hign.integral_respInd_arm_mul hW hA hY hps a hg).1]
  refine integrable_congr ?_
  filter_upwards [hpos] with ω hω
  field_simp

/-- **Second moment of the weighted outcome:** `E[(w_a Y)²] = E[Y(a)² / π_a(W)]` under the
indicator form of ignorability and positivity of the arm. The two sides are integrals of
functions that are integrable together (`IndicatorIgnorable.integrable_ipwTerm_sq_iff`); when
they are not, both integrals are `0` by convention, so the identity is a statement about second
moments only when `Y(a)² / π_a(W)` is integrable. -/
theorem IndicatorIgnorable.integral_ipwTerm_sq [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) :
    ∫ ω, ipwTerm A Y W e a ω ^ 2 ∂μ = ∫ ω, Y a ω ^ 2 / armProb e a (W ω) ∂μ := by
  have hsq : (fun ω => ipwTerm A Y W e a ω ^ 2) =
      fun ω => respInd (arm A a) ω * (fun q : 𝒲 × ℝ => q.2 ^ 2 / armProb e a q.1 ^ 2)
        (W ω, Y a ω) := by
    funext ω
    have h1 := respInd_arm_mul_obsOutcome A Y a ω
    have h2 := respInd_mul_self (arm A a) ω
    simp only [ipwTerm]
    calc (respInd (arm A a) ω * obsOutcome A Y ω / armProb e a (W ω)) ^ 2
        = (respInd (arm A a) ω * obsOutcome A Y ω) * (respInd (arm A a) ω * obsOutcome A Y ω) /
          armProb e a (W ω) ^ 2 := by ring
      _ = (respInd (arm A a) ω * respInd (arm A a) ω) * (Y a ω ^ 2 / armProb e a (W ω) ^ 2) := by
          rw [h1]; ring
      _ = _ := by rw [h2]
  have hg : Measurable fun q : 𝒲 × ℝ => q.2 ^ 2 / armProb e a q.1 ^ 2 :=
    (measurable_snd.pow_const 2).div
      (((measurable_armProb hps.1 a).comp measurable_fst).pow_const 2)
  rw [hsq, (hign.integral_respInd_arm_mul hW hA hY hps a hg).2]
  refine integral_congr_ae ?_
  filter_upwards [hpos] with ω hω
  field_simp

/-- **Variance of the weighted outcome**: `Var(w_a Y) = E[Y(a)² / π_a(W)] - E[Y(a)]²` under the
indicator form of ignorability and positivity of the arm, when `Y(a)² / π_a(W)` is
integrable. -/
theorem IndicatorIgnorable.variance_ipwTerm [IsProbabilityMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hYi : Integrable (Y a) μ) (hint : Integrable (fun ω => Y a ω ^ 2 / armProb e a (W ω)) μ) :
    variance (ipwTerm A Y W e a) μ =
      ∫ ω, Y a ω ^ 2 / armProb e a (W ω) ∂μ - armMean μ Y a ^ 2 := by
  have hm := measurable_ipwTerm hW hA hY hps.1 a
  have hL2 : MemLp (ipwTerm A Y W e a) 2 μ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
      ((hign.integrable_ipwTerm_sq_iff hW hA hY hps a hpos).2 hint)
  rw [variance_eq_sub hL2]
  change ∫ ω, ipwTerm A Y W e a ω ^ 2 ∂μ - (∫ ω, ipwTerm A Y W e a ω ∂μ) ^ 2 = _
  rw [hign.integral_ipwTerm_sq hW hA hY hps a hpos]
  have h := hign.armMean_eq_ipw hW hA hY hps a hpos hYi
  rw [h]
  rfl

/-! ### Bias under a wrong score -/

/-- **Bias of the Horvitz and Thompson arm mean under a wrong score.** Let `e` be the true
propensity score and `ê` any measurable score. Under the indicator form of ignorability, if
`Y(a)` and the weighted outcome `1{A = a} Y / π̂_a(W)` are integrable, then
`E[1{A = a} Y / π̂_a(W)] - E[Y(a)] = E[(π_a(W) / π̂_a(W) - 1) E[Y(a) | W]]`. The identity needs
no positivity of `ê`; it is the bias of a weighting estimator when `π̂_a(W) > 0` almost surely
(where `π̂_a(W) = 0` both weights read `x / 0 = 0`). -/
theorem IndicatorIgnorable.ipwArmMean_sub_armMean [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) {e' : 𝒲 → ℝ} (he' : Measurable e')
    (hYi : Integrable (Y a) μ) (hint : Integrable (ipwTerm A Y W e' a) μ) :
    ipwArmMean μ A Y W e' a - armMean μ Y a =
      ∫ ω, (armProb e a (W ω) / armProb e' a (W ω) - 1) *
        μ[Y a | MeasurableSpace.comap W inferInstance] ω ∂μ := by
  have hp' := measurable_armProb he' a
  have hp := measurable_armProb hps.1 a
  have hg : Measurable fun q : 𝒲 × ℝ => q.2 / armProb e' a q.1 :=
    measurable_snd.div (hp'.comp measurable_fst)
  have hterm : ipwTerm A Y W e' a =
      fun ω => respInd (arm A a) ω * (fun q : 𝒲 × ℝ => q.2 / armProb e' a q.1) (W ω, Y a ω) := by
    funext ω
    simp only [ipwTerm]
    rw [respInd_arm_mul_obsOutcome, mul_div_assoc]
  obtain ⟨hiff, e1⟩ := hign.integral_respInd_arm_mul hW hA hY hps a hg
  rw [hterm] at hint
  have hint1 := hiff.1 hint
  -- second step: condition on `W`
  have hgW : StronglyMeasurable[MeasurableSpace.comap W inferInstance]
      (fun ω => armProb e a (W ω) / armProb e' a (W ω)) :=
    ((hp.div hp').comp (comap_measurable W)).stronglyMeasurable
  have hint2 : Integrable (fun ω => Y a ω * (armProb e a (W ω) / armProb e' a (W ω))) μ :=
    hint1.congr (Filter.Eventually.of_forall fun ω => by simp only; ring)
  obtain ⟨hint3, e2⟩ := integral_mul_eq_of_condExp_eq hW.comap_le hYi hgW hint2
    (Filter.EventuallyEq.refl _ _)
  have hc : Integrable (μ[Y a | MeasurableSpace.comap W inferInstance]) μ := integrable_condExp
  rw [ipwArmMean, hterm, e1, armMean]
  calc ∫ ω, armProb e a (W ω) * (Y a ω / armProb e' a (W ω)) ∂μ - ∫ ω, Y a ω ∂μ
      = ∫ ω, Y a ω * (armProb e a (W ω) / armProb e' a (W ω)) ∂μ -
          ∫ ω, μ[Y a | MeasurableSpace.comap W inferInstance] ω ∂μ := by
        rw [integral_condExp hW.comap_le]
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
    _ = ∫ ω, (μ[Y a | MeasurableSpace.comap W inferInstance] ω *
          (armProb e a (W ω) / armProb e' a (W ω)) -
            μ[Y a | MeasurableSpace.comap W inferInstance] ω) ∂μ := by
        rw [e2, integral_sub hint3 hc]
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)

end PointTreatment

end CausalInference
