/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Weighting
public import CausalInference.Measures.LinkScale

/-!
# Point treatment: the weighted arm mean under poor overlap

The exact variance of the Horvitz and Thompson term of an arm is
`Var(w_a Y) = E[Y(a)² / π_a(W)] - E[Y(a)]²` (`IndicatorIgnorable.variance_ipwTerm`). This file
draws the consequences of poor overlap.

* **Lower bound.** If the conditional second moment `E[Y(a)² | W]` is at least `c` almost
  surely, the variance is at least `c E[1 / π_a(W)] - E[Y(a)]²`.
* **Divergence.** Along a sequence of populations in which `E[1 / π_a(W)]` tends to infinity,
  with the conditional second moments bounded below by a fixed `c > 0` and bounded means, the
  variance tends to infinity. A vanishing minimum propensity alone is not enough: the variance
  is governed by the mean of `1 / π_a(W)`, which can stay bounded while the smallest propensity
  tends to zero.
* **Effective sample size.** The effective sample size fraction of the inverse probability
  weights is `1 / E[1 / π_a(W)]` (`essFraction_ipwWeight`). It is at most
  `E[π_a(W)] = P(A = a)`, with equality exactly when `π_a(W)` is almost surely constant.

## Main results

* `IndicatorIgnorable.le_variance_ipwTerm`: the lower bound.
* `tendsto_atTop_of_le_mul_sub`, `IndicatorIgnorable.tendsto_variance_ipwTerm_atTop`: the
  divergence.
* `integral_armProb_comp`: `E[π_a(W)] = P(A = a)`.
* `inv_integral_inv_le_integral`, `inv_integral_inv_eq_integral_iff`: the inequality
  `1 / E[1 / X] ≤ E[X]` for a positive random variable, with its equality case.
* `essFraction_ipwWeight_le_measureReal`, `essFraction_ipwWeight_eq_measureReal_iff`.

## References

* R. K. Crump, V. J. Hotz, G. W. Imbens and O. A. Mitnik, *Dealing with limited overlap in
  estimation of average treatment effects*, Biometrika 96 (2009).
* L. Kish, *Survey Sampling*, Wiley, 1965.
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData Filter Topology

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲] {μ : Measure Ω}
  {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {e : 𝒲 → ℝ}

/-! ### The lower bound and divergence -/

/-- **Lower bound on the variance of the weighted outcome.** Under the indicator form of
ignorability, positivity of the arm, integrable `Y(a)`, `Y(a)² / π_a(W)` and `1 / π_a(W)`, and
a conditional second moment `E[Y(a)² | W] ≥ c` almost surely,
`c E[1 / π_a(W)] - E[Y(a)]² ≤ Var(w_a Y)`. -/
theorem IndicatorIgnorable.le_variance_ipwTerm [IsProbabilityMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hYi : Integrable (Y a) μ) (hint : Integrable (fun ω => Y a ω ^ 2 / armProb e a (W ω)) μ)
    (hinv : Integrable (fun ω => 1 / armProb e a (W ω)) μ) {c : ℝ}
    (hc : ∀ᵐ ω ∂μ, c ≤ μ[fun ω => Y a ω ^ 2 | MeasurableSpace.comap W inferInstance] ω) :
    c * ∫ ω, 1 / armProb e a (W ω) ∂μ - armMean μ Y a ^ 2 ≤ variance (ipwTerm A Y W e a) μ := by
  rw [hign.variance_ipwTerm hW hA hY hps a hpos hYi hint]
  gcongr
  set m := MeasurableSpace.comap W inferInstance
  have hle1 : ∀ᵐ ω ∂μ, armProb e a (W ω) ≤ 1 := by
    filter_upwards [hps.ae_mem_Icc hW hA] with ω h
    cases a <;> simp only [armProb_true, armProb_false] <;> linarith [h.1, h.2]
  -- `Y(a)²` is integrable since it is dominated by `Y(a)² / π_a(W)`.
  have hY2 : Integrable (fun ω => Y a ω ^ 2) μ := by
    refine hint.mono' ((hY a).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hpos, hle1] with ω hp h1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_div_self (sq_nonneg _) hp h1
  have hinvm : StronglyMeasurable[m] (fun ω => 1 / armProb e a (W ω)) :=
    (measurable_const.div ((measurable_armProb hps.1 a).comp
      (comap_measurable W))).stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_left hinvm
    (hint.congr (Eventually.of_forall fun ω => by simp only [Pi.mul_apply]; ring)) hY2
  have hint' : Integrable (fun ω => (1 / armProb e a (W ω)) *
      μ[fun ω => Y a ω ^ 2 | m] ω) μ :=
    (integrable_condExp (m := m) (μ := μ)
      (f := fun ω => (1 / armProb e a (W ω)) * Y a ω ^ 2)).congr hpull
  calc c * ∫ ω, 1 / armProb e a (W ω) ∂μ
      = ∫ ω, 1 / armProb e a (W ω) * c ∂μ := by rw [integral_mul_const, mul_comm]
    _ ≤ ∫ ω, (1 / armProb e a (W ω)) * μ[fun ω => Y a ω ^ 2 | m] ω ∂μ := by
        refine integral_mono_ae (hinv.mul_const c) hint' ?_
        filter_upwards [hc, hpos] with ω h hp
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = ∫ ω, μ[fun ω => (1 / armProb e a (W ω)) * Y a ω ^ 2 | m] ω ∂μ :=
        integral_congr_ae (hpull.symm.trans (Eventually.of_forall fun _ => rfl))
    _ = ∫ ω, Y a ω ^ 2 / armProb e a (W ω) ∂μ := by
        rw [integral_condExp (comap_le_of_measurable' hW)]
        congr 1; funext ω; ring
where
  comap_le_of_measurable' (hW : Measurable W) :
      MeasurableSpace.comap W inferInstance ≤ mΩ := hW.comap_le

/-- **Divergence from a lower bound.** If `c * I n - m n ^ 2 ≤ V n` with `c > 0`,
`I n → ∞` and `|m n| ≤ M`, then `V n → ∞`. -/
theorem tendsto_atTop_of_le_mul_sub {V I m : ℕ → ℝ} {c M : ℝ} (hc : 0 < c)
    (hI : Tendsto I atTop atTop) (hm : ∀ n, |m n| ≤ M) (hV : ∀ n, c * I n - m n ^ 2 ≤ V n) :
    Tendsto V atTop atTop := by
  have h1 : Tendsto (fun n => c * I n - M ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hI.const_mul_atTop hc)
  refine tendsto_atTop_mono (fun n => ?_) h1
  have : m n ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hm n) 2
  linarith [hV n]

/-- **The variance of the weighted outcome diverges under vanishing overlap.** Take a sequence
of populations `(μ n, A n, W n, Y n, e n)` satisfying, for each `n`, the indicator form of
ignorability, positivity of the arm, the integrability conditions and a conditional second
moment `E[Y(a)² | W] ≥ c` with a fixed `c > 0`. If `E[1 / π_a(W)]` tends to infinity and the
arm means `E[Y(a)]` stay bounded, the variance of `w_a Y` tends to infinity. -/
theorem IndicatorIgnorable.tendsto_variance_ipwTerm_atTop {μ : ℕ → Measure Ω}
    [∀ n, IsProbabilityMeasure (μ n)] {A : ℕ → Ω → Bool} {W : ℕ → Ω → 𝒲}
    {Y : ℕ → Bool → Ω → ℝ} {e : ℕ → 𝒲 → ℝ} (a : Bool) (hW : ∀ n, Measurable (W n))
    (hA : ∀ n, Measurable (A n)) (hY : ∀ n a, Measurable (Y n a))
    (hign : ∀ n, IndicatorIgnorable (μ n) (A n) (W n) (Y n))
    (hps : ∀ n, IsPropensityScore (μ n) (A n) (W n) (e n))
    (hpos : ∀ n, ∀ᵐ ω ∂(μ n), 0 < armProb (e n) a (W n ω))
    (hYi : ∀ n, Integrable (Y n a) (μ n))
    (hint : ∀ n, Integrable (fun ω => Y n a ω ^ 2 / armProb (e n) a (W n ω)) (μ n))
    (hinv : ∀ n, Integrable (fun ω => 1 / armProb (e n) a (W n ω)) (μ n)) {c M : ℝ}
    (hc0 : 0 < c) (hc : ∀ n, ∀ᵐ ω ∂(μ n),
      c ≤ (μ n)[fun ω => Y n a ω ^ 2 | MeasurableSpace.comap (W n) inferInstance] ω)
    (hdiv : Tendsto (fun n => ∫ ω, 1 / armProb (e n) a (W n ω) ∂(μ n)) atTop atTop)
    (hM : ∀ n, |armMean (μ n) (Y n) a| ≤ M) :
    Tendsto (fun n => variance (ipwTerm (A n) (Y n) (W n) (e n) a) (μ n)) atTop atTop :=
  tendsto_atTop_of_le_mul_sub hc0 hdiv hM fun n =>
    (hign n).le_variance_ipwTerm (hW n) (hA n) (hY n) (hps n) a (hpos n) (hYi n) (hint n)
      (hinv n) (hc n)

/-! ### The effective sample size -/

/-- **The mean of the arm propensity is the arm probability**: `E[π_a(W)] = P(A = a)`. -/
theorem integral_armProb_comp [IsFiniteMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hps : IsPropensityScore μ A W e) (a : Bool) :
    ∫ ω, armProb e a (W ω) ∂μ = μ.real (A ⁻¹' {a}) := by
  have hs : MeasurableSet (A ⁻¹' {a}) := hA (measurableSet_singleton a)
  have hind : respInd (arm A a) = (A ⁻¹' {a}).indicator 1 := by
    funext ω
    rw [respInd_arm_apply]
    by_cases h : A ω = a <;> simp [Set.indicator, h]
  rw [← integral_congr_ae (hps.condExp_arm hW hA a), integral_condExp hW.comap_le, hind,
    integral_indicator_one hs]

/-- **The harmonic mean is at most the mean.** For an almost surely positive random variable
`X` with `X` and `1 / X` integrable, `1 / E[1 / X] ≤ E[X]`. The integral of the nonnegative
function `(X - E[X])² / (X E[X]²)` is `E[1 / X] - 1 / E[X]`. -/
theorem inv_integral_inv_le_integral [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hpos : ∀ᵐ ω ∂μ, 0 < X ω) (hX : Integrable X μ) (hinv : Integrable (fun ω => 1 / X ω) μ) :
    1 / ∫ ω, 1 / X ω ∂μ ≤ ∫ ω, X ω ∂μ := by
  have hm : 0 < ∫ ω, X ω ∂μ := EffectMeasure.integral_pos_of_ae_pos hX hpos
  have hI : 0 < ∫ ω, 1 / X ω ∂μ :=
    EffectMeasure.integral_pos_of_ae_pos hinv (hpos.mono fun ω h => by positivity)
  set m := ∫ ω, X ω ∂μ
  have hg : (fun ω => (X ω - m) ^ 2 / (X ω * m ^ 2)) =ᵐ[μ]
      fun ω => X ω / m ^ 2 - 2 / m + 1 / X ω := by
    filter_upwards [hpos] with ω h
    field_simp
    ring
  have hint : Integrable (fun ω => X ω / m ^ 2 - 2 / m + 1 / X ω) μ :=
    ((hX.div_const _).sub (integrable_const _)).add hinv
  have hval : ∫ ω, (X ω - m) ^ 2 / (X ω * m ^ 2) ∂μ = ∫ ω, 1 / X ω ∂μ - 1 / m := by
    rw [integral_congr_ae hg,
      integral_add (f := fun ω => X ω / m ^ 2 - 2 / m) (g := fun ω => 1 / X ω)
        ((hX.div_const _).sub (integrable_const _)) hinv,
      integral_sub (f := fun ω => X ω / m ^ 2) (g := fun _ => 2 / m) (hX.div_const _)
        (integrable_const _), integral_div, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    field_simp
    ring
  have h0 : 0 ≤ ∫ ω, (X ω - m) ^ 2 / (X ω * m ^ 2) ∂μ :=
    integral_nonneg_of_ae (by filter_upwards [hpos] with ω h; positivity)
  rw [div_le_iff₀ hI]
  rw [hval] at h0
  have : 1 / m ≤ ∫ ω, 1 / X ω ∂μ := by linarith
  rw [div_le_iff₀ hm] at this
  linarith

/-- **The equality case of the harmonic and arithmetic means.** Under the hypotheses of
`inv_integral_inv_le_integral`, `1 / E[1 / X] = E[X]` exactly when `X` is almost surely equal to
the constant `E[X]`. -/
theorem inv_integral_inv_eq_integral_iff [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hpos : ∀ᵐ ω ∂μ, 0 < X ω) (hX : Integrable X μ) (hinv : Integrable (fun ω => 1 / X ω) μ) :
    1 / ∫ ω, 1 / X ω ∂μ = ∫ ω, X ω ∂μ ↔ X =ᵐ[μ] fun _ => ∫ ω, X ω ∂μ := by
  have hm : 0 < ∫ ω, X ω ∂μ := EffectMeasure.integral_pos_of_ae_pos hX hpos
  have hI : 0 < ∫ ω, 1 / X ω ∂μ :=
    EffectMeasure.integral_pos_of_ae_pos hinv (hpos.mono fun ω h => by positivity)
  set m := ∫ ω, X ω ∂μ
  set f : Ω → ℝ := fun ω => (X ω - m) ^ 2 / (X ω * m ^ 2)
  have hg : f =ᵐ[μ] fun ω => X ω / m ^ 2 - 2 / m + 1 / X ω := by
    filter_upwards [hpos] with ω h
    simp only [f]
    field_simp
    ring
  have hfi : Integrable f μ :=
    (((hX.div_const _).sub (integrable_const _)).add hinv).congr hg.symm
  have hval : ∫ ω, f ω ∂μ = ∫ ω, 1 / X ω ∂μ - 1 / m := by
    rw [integral_congr_ae hg,
      integral_add (f := fun ω => X ω / m ^ 2 - 2 / m) (g := fun ω => 1 / X ω)
        ((hX.div_const _).sub (integrable_const _)) hinv,
      integral_sub (f := fun ω => X ω / m ^ 2) (g := fun _ => 2 / m) (hX.div_const _)
        (integrable_const _), integral_div, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    field_simp
    ring
  have hf0 : 0 ≤ᵐ[μ] f := by
    filter_upwards [hpos] with ω h
    simp only [f, Pi.zero_apply]
    positivity
  have key : 1 / ∫ ω, 1 / X ω ∂μ = m ↔ ∫ ω, f ω ∂μ = 0 := by
    rw [hval, sub_eq_zero]
    constructor
    · intro h; rw [← h]; field_simp
    · intro h; rw [h]; field_simp
  rw [key, integral_eq_zero_iff_of_nonneg_ae hf0 hfi]
  constructor
  · intro h
    filter_upwards [h, hpos] with ω h1 h2
    simp only [f, Pi.zero_apply, div_eq_zero_iff, pow_eq_zero_iff two_ne_zero, sub_eq_zero,
      mul_eq_zero, h2.ne', hm.ne', or_false] at h1
    exact h1
  · intro h
    filter_upwards [h] with ω h1
    simp [f, h1]

/-- **The effective sample size fraction is at most the arm probability.** At the true score,
with positivity of the arm and integrable `1 / π_a(W)`,
`essFraction (w_a) = 1 / E[1 / π_a(W)] ≤ E[π_a(W)] = P(A = a)`. -/
theorem essFraction_ipwWeight_le_measureReal [IsProbabilityMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hint : Integrable (fun ω => 1 / armProb e a (W ω)) μ) :
    essFraction μ (ipwWeight A W e a) ≤ μ.real (A ⁻¹' {a}) := by
  rw [essFraction_ipwWeight hW hA hps a hpos hint, ← integral_armProb_comp hW hA hps a]
  exact inv_integral_inv_le_integral hpos (integrable_armProb_comp hW hA hps a) hint
where
  integrable_armProb_comp (hW : Measurable W) (hA : Measurable A)
      (hps : IsPropensityScore μ A W e) (a : Bool) :
      Integrable (fun ω => armProb e a (W ω)) μ :=
    (integrable_condExp (m := MeasurableSpace.comap W inferInstance) (μ := μ)
      (f := respInd (arm A a))).congr (hps.condExp_arm hW hA a)

/-- **The equality case of the effective sample size.** Under the hypotheses of
`essFraction_ipwWeight_le_measureReal`, the effective sample size fraction equals the arm
probability `P(A = a)` exactly when `π_a(W) = P(A = a)` almost surely, that is when the
propensity of the arm does not vary with the covariates. -/
theorem essFraction_ipwWeight_eq_measureReal_iff [IsProbabilityMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hint : Integrable (fun ω => 1 / armProb e a (W ω)) μ) :
    essFraction μ (ipwWeight A W e a) = μ.real (A ⁻¹' {a}) ↔
      (fun ω => armProb e a (W ω)) =ᵐ[μ] fun _ => μ.real (A ⁻¹' {a}) := by
  rw [essFraction_ipwWeight hW hA hps a hpos hint, ← integral_armProb_comp hW hA hps a]
  exact inv_integral_inv_eq_integral_iff hpos
    (essFraction_ipwWeight_le_measureReal.integrable_armProb_comp hW hA hps a) hint

end PointTreatment

end CausalInference
