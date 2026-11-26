/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Sign.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.ConditionalProbability
public import CausalInference.PartialIdentification.IdentifiedSet

/-!
# Manski bounds for a binary treatment with bounded outcomes

Worst-case (no-assumption) bounds on the integrated potential outcomes and on the integrated
treatment effect, their sharpness by explicit construction, and their tightening under
monotone treatment response.

## Setting

Measure-theoretic. A measurable space `Ω` with a finite measure `μ`, a measurable binary
treatment `A : Ω → Bool`, and a potential outcome model `m : POModel Ω` with measurable
potential outcomes `m.Y1`, `m.Y0` taking values in `[lo, hi]`. The observed outcome is
`Y = if A then Y1 else Y0`.

The parameters are the integrals `∫ Y1 dμ`, `∫ Y0 dμ` and the integrated treatment effect
`∫ Y1 dμ - ∫ Y0 dμ`. When `μ` is a probability measure these are the means `E[Y1]`, `E[Y0]`
and the average treatment effect, and `μ(A = 0)` is `P(A = 0)`; results that need total mass
one (`ate_bounds_width`, `not_pointIdentified_ate`, `not_pointIdentified_sign_ate`) assume
`IsProbabilityMeasure μ`. For a general finite measure the endpoints of the bounds on the
integrated treatment effect differ by `(hi - lo) * μ(Ω)` (`ate_bounds_width_finite`).

For the main identified set statements the observation is the realized outcome function
`observed A m : Ω → ℝ` on the fixed `(Ω, μ)` with the fixed treatment `A`; models vary only in
their potential outcomes. The bounds depend on this observation only through the two arm
integrals `∫_{A = 1} Y dμ` and `∫_{A = 0} Y dμ`, and the last section transfers the identified
sets to the coarser observations given by these arm integrals and by the joint law of `(A, Y)`.

## Main results

* `meanY1_mem_Icc`, `meanY0_mem_Icc`: for every bounded model,
  `∫_{A = 1} Y dμ + lo μ(A = 0) ≤ ∫ Y1 dμ ≤ ∫_{A = 1} Y dμ + hi μ(A = 0)`, and similarly for
  `∫ Y0 dμ`.
* `boundY1_eq_cond`, `boundY0_eq_cond`: the textbook form
  `E[Y | A = 1] P(A = 1) + lo P(A = 0)` of the bounds, via the conditional measure.
* `ate_mem_Icc`: the resulting bounds on the integrated treatment effect;
  `ate_bounds_width_finite`, `ate_bounds_width`: their endpoints differ by `(hi - lo) * μ(Ω)`,
  which is `hi - lo` for a probability measure.
* `exists_model_meanY1_eq`, `exists_model_meanY0_eq`, `exists_model_ate_eq`: sharpness by
  explicit construction.
* `identifiedSet_meanY1`, `identifiedSet_meanY0`, `identifiedSet_ate`: the identified sets (in
  the sense of `CausalInference.identifiedSet`) are exactly the closed intervals.
* `not_pointIdentified_meanY1`, `not_pointIdentified_ate`: non-identification when `lo < hi`
  (with a control group of positive mass, respectively a probability measure), together with
  the observation-specific forms `not_subsingleton_identifiedSet_meanY1` and
  `not_subsingleton_identifiedSet_ate`.
* `zero_mem_ate_bounds`: the no-assumption bounds on the effect always contain zero, and
  `not_pointIdentified_sign_ate`: the sign of the effect is not identified.
* `meanY1_mem_Icc_of_mem_mtrModels`, `meanY0_mem_Icc_of_mem_mtrModels`,
  `identifiedSet_meanY1_mtr`, `identifiedSet_meanY0_mtr`: under monotone treatment response
  the identified sets for `∫ Y1 dμ` and `∫ Y0 dμ` are `[∫ Y dμ, boundY1 hi]` and
  `[boundY0 lo, ∫ Y dμ]`.
* `ate_mem_Icc_of_mem_mtrModels`, `exists_mtr_model_ate_eq`, `identifiedSet_ate_mtr`: under
  monotone treatment response the identified set for the integrated treatment effect is
  exactly `[0, boundY1 hi - boundY0 lo]`.
* `identifiedSet_meanY1_armIntegrals`, `identifiedSet_meanY0_armIntegrals`,
  `identifiedSet_ate_armIntegrals`, `identifiedSet_meanY1_jointLaw`,
  `identifiedSet_meanY0_jointLaw`, `identifiedSet_ate_jointLaw`: the same intervals are the
  identified sets when only the arm integrals, or only the joint law of `(A, Y)`, is observed.

## References

* C. F. Manski, Nonparametric bounds on treatment effects, *American Economic Review* 80
  (1990).
* C. F. Manski, Monotone treatment response, *Econometrica* 65 (1997).
* C. F. Manski, *Partial Identification of Probability Distributions*, Springer, 2003.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalInference

namespace Manski

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Core estimate: if `f` is measurable with values in `[lo, hi]` and agrees with `y` on a
measurable set `s`, then `∫ f` lies between `∫_s y + lo μ(sᶜ)` and `∫_s y + hi μ(sᶜ)`. -/
theorem integral_mem_Icc_of_eqOn [IsFiniteMeasure μ] {lo hi : ℝ} {s : Set Ω}
    (hs : MeasurableSet s) {f y : Ω → ℝ} (hf : Measurable f) (hfb : ∀ ω, f ω ∈ Icc lo hi)
    (hfy : EqOn f y s) :
    ∫ ω, f ω ∂μ ∈ Icc (∫ ω in s, y ω ∂μ + lo * μ.real sᶜ) (∫ ω in s, y ω ∂μ + hi * μ.real sᶜ) := by
  have hfi : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable (max |lo| |hi|) (ae_of_all _ fun ω =>
      abs_le_max_abs_abs (hfb ω).1 (hfb ω).2)
  rw [← integral_add_compl hs hfi, setIntegral_congr_fun hs hfy]
  have h1 : lo * μ.real sᶜ ≤ ∫ ω in sᶜ, f ω ∂μ :=
    setIntegral_ge_of_const_le_real hs.compl (measure_ne_top _ _) (fun ω _ => (hfb ω).1)
      hfi.integrableOn
  have h2 : ∫ ω in sᶜ, f ω ∂μ ≤ hi * μ.real sᶜ := by
    rw [mul_comm, ← smul_eq_mul, ← setIntegral_const]
    exact setIntegral_mono_on hfi.integrableOn (integrableOn_const (measure_ne_top _ _))
      hs.compl fun ω _ => (hfb ω).2
  constructor <;> linarith

/-- A bounded measurable real function on a finite measure space is integrable. -/
theorem integrable_of_mem_Icc [IsFiniteMeasure μ] {lo hi : ℝ} {f : Ω → ℝ} (hf : Measurable f)
    (hfb : ∀ ω, f ω ∈ Icc lo hi) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable (max |lo| |hi|) (ae_of_all _ fun ω =>
    abs_le_max_abs_abs (hfb ω).1 (hfb ω).2)

/-- A potential outcome model on the sample space `Ω`: the treated potential outcome `Y1` and
the control potential outcome `Y0`, both real-valued. -/
structure POModel (Ω : Type*) where
  /-- Potential outcome under treatment. -/
  Y1 : Ω → ℝ
  /-- Potential outcome under control. -/
  Y0 : Ω → ℝ

/-- The treated event `{A = 1}` of a binary treatment `A : Ω → Bool`. -/
def treated (A : Ω → Bool) : Set Ω := {ω | A ω = true}

theorem measurableSet_treated {A : Ω → Bool} (hA : Measurable A) : MeasurableSet (treated A) :=
  hA (measurableSet_singleton true)

/-- The observed outcome `Y = Y1` on `{A = 1}` and `Y = Y0` on `{A = 0}` (consistency). -/
def observed (A : Ω → Bool) (m : POModel Ω) : Ω → ℝ :=
  fun ω => if A ω then m.Y1 ω else m.Y0 ω

/-- The model class with no assumption beyond bounded outcomes: both potential outcomes are
measurable with values in `[lo, hi]`. -/
def boundedModels (lo hi : ℝ) : Set (POModel Ω) :=
  {m | Measurable m.Y1 ∧ Measurable m.Y0 ∧ (∀ ω, m.Y1 ω ∈ Icc lo hi) ∧ ∀ ω, m.Y0 ω ∈ Icc lo hi}

/-- Bounded models satisfying monotone treatment response: `Y0 ≤ Y1` pointwise. -/
def mtrModels (lo hi : ℝ) : Set (POModel Ω) :=
  {m | m ∈ boundedModels lo hi ∧ ∀ ω, m.Y0 ω ≤ m.Y1 ω}

/-- The integral `∫ Y1 dμ` of the treated potential outcome; the mean `E[Y1]` when `μ` is a
probability measure. -/
noncomputable def meanY1 (μ : Measure Ω) (m : POModel Ω) : ℝ := ∫ ω, m.Y1 ω ∂μ

/-- The integral `∫ Y0 dμ` of the control potential outcome; the mean `E[Y0]` when `μ` is a
probability measure. -/
noncomputable def meanY0 (μ : Measure Ω) (m : POModel Ω) : ℝ := ∫ ω, m.Y0 ω ∂μ

/-- The integrated treatment effect `∫ Y1 dμ - ∫ Y0 dμ`; the average treatment effect
`E[Y1] - E[Y0]` when `μ` is a probability measure. -/
noncomputable def ate (μ : Measure Ω) (m : POModel Ω) : ℝ := meanY1 μ m - meanY0 μ m

/-- The Manski bound for `∫ Y1 dμ` with fill value `c`: `∫_{A = 1} y dμ + c μ(A = 0)`. With
`c = lo` it is the lower bound, with `c = hi` the upper bound. It depends only on observed
data. -/
noncomputable def boundY1 (μ : Measure Ω) (A : Ω → Bool) (c : ℝ) (y : Ω → ℝ) : ℝ :=
  ∫ ω in treated A, y ω ∂μ + c * μ.real (treated A)ᶜ

/-- The Manski bound for `∫ Y0 dμ` with fill value `c`: `∫_{A = 0} y dμ + c μ(A = 1)`. -/
noncomputable def boundY0 (μ : Measure Ω) (A : Ω → Bool) (c : ℝ) (y : Ω → ℝ) : ℝ :=
  ∫ ω in (treated A)ᶜ, y ω ∂μ + c * μ.real (treated A)

/-- The integral of `y` over a set `s` is the mass of `s` times the integral of `y` against the
conditional measure `μ[|s] = μ(s)⁻¹ • μ.restrict s`. When `0 < μ(s)` the second factor is the
conditional mean of `y` given `s`; when `μ(s) = 0` both sides are zero. The identity holds for
every `y`; for a `y` that is not integrable on `s` both integrals take Lean's default value
zero, so the statement carries content only for integrable `y`, as for the bounded outcomes
used in this file. -/
theorem setIntegral_eq_measureReal_mul_cond [IsFiniteMeasure μ] (s : Set Ω) (y : Ω → ℝ) :
    ∫ ω in s, y ω ∂μ = μ.real s * ∫ ω, y ω ∂(ProbabilityTheory.cond μ s) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    ← mul_assoc]
  by_cases h : μ.real s = 0
  · have hs : μ s = 0 := (measureReal_eq_zero_iff (measure_ne_top μ s)).1 h
    rw [Measure.restrict_eq_zero.2 hs, integral_zero_measure, mul_zero]
  · rw [measureReal_def] at h
    rw [measureReal_def, mul_inv_cancel₀ h, one_mul]

variable {A : Ω → Bool} {lo hi : ℝ}

/-- The textbook form of the Manski bound for `∫ Y1 dμ`: the treated mass times the
conditional mean of `y` among the treated, plus `c` times the control mass. For a probability
measure with `0 < P(A = 1)` this reads `E[Y | A = 1] P(A = 1) + c P(A = 0)`. -/
theorem boundY1_eq_cond [IsFiniteMeasure μ] (c : ℝ) (y : Ω → ℝ) :
    boundY1 μ A c y = μ.real (treated A) * ∫ ω, y ω ∂(ProbabilityTheory.cond μ (treated A)) +
      c * μ.real (treated A)ᶜ := by
  rw [boundY1, setIntegral_eq_measureReal_mul_cond]

/-- The textbook form of the Manski bound for `∫ Y0 dμ`: for a probability measure with
`0 < P(A = 0)` it reads `E[Y | A = 0] P(A = 0) + c P(A = 1)`. -/
theorem boundY0_eq_cond [IsFiniteMeasure μ] (c : ℝ) (y : Ω → ℝ) :
    boundY0 μ A c y = μ.real (treated A)ᶜ * ∫ ω, y ω ∂(ProbabilityTheory.cond μ (treated A)ᶜ) +
      c * μ.real (treated A) := by
  rw [boundY0, setIntegral_eq_measureReal_mul_cond]

/-- No-assumption bounds on `∫ Y1 dμ` (Manski 1990): for every bounded model,
`∫_{A = 1} Y dμ + lo μ(A = 0) ≤ ∫ Y1 dμ ≤ ∫_{A = 1} Y dμ + hi μ(A = 0)`, where `Y` is the
observed outcome. -/
theorem meanY1_mem_Icc [IsFiniteMeasure μ] (hA : Measurable A) {m : POModel Ω}
    (hm : m ∈ boundedModels lo hi) :
    meanY1 μ m ∈ Icc (boundY1 μ A lo (observed A m)) (boundY1 μ A hi (observed A m)) :=
  integral_mem_Icc_of_eqOn (measurableSet_treated hA) hm.1 hm.2.2.1 fun ω hω => by
    simp [observed, show A ω = true from hω]

/-- No-assumption bounds on `∫ Y0 dμ`:
`∫_{A = 0} Y dμ + lo μ(A = 1) ≤ ∫ Y0 dμ ≤ ∫_{A = 0} Y dμ + hi μ(A = 1)`. -/
theorem meanY0_mem_Icc [IsFiniteMeasure μ] (hA : Measurable A) {m : POModel Ω}
    (hm : m ∈ boundedModels lo hi) :
    meanY0 μ m ∈ Icc (boundY0 μ A lo (observed A m)) (boundY0 μ A hi (observed A m)) := by
  have h := integral_mem_Icc_of_eqOn (μ := μ) (measurableSet_treated hA).compl hm.2.1 hm.2.2.2
    (y := observed A m) fun ω hω => by
      simp [observed, show A ω = false by simpa [treated] using hω]
  rwa [compl_compl] at h

/-- No-assumption bounds on the integrated treatment effect:
`boundY1 lo - boundY0 hi ≤ ∫ Y1 dμ - ∫ Y0 dμ ≤ boundY1 hi - boundY0 lo`. -/
theorem ate_mem_Icc [IsFiniteMeasure μ] (hA : Measurable A) {m : POModel Ω}
    (hm : m ∈ boundedModels lo hi) :
    ate μ m ∈ Icc (boundY1 μ A lo (observed A m) - boundY0 μ A hi (observed A m))
      (boundY1 μ A hi (observed A m) - boundY0 μ A lo (observed A m)) := by
  have h1 := meanY1_mem_Icc (μ := μ) hA hm
  have h0 := meanY0_mem_Icc (μ := μ) hA hm
  exact ⟨by unfold ate; linarith [h1.1, h0.2], by unfold ate; linarith [h1.2, h0.1]⟩

/-- For a finite measure, the upper endpoint minus the lower endpoint of the no-assumption
bounds on the integrated treatment effect is exactly `(hi - lo) * μ(Ω)`, whatever the observed
data. This is an algebraic identity: it holds for every `y` and also when `hi < lo`, in which
case the difference is negative and there is no interval to speak of. -/
theorem ate_bounds_width_finite [IsFiniteMeasure μ] (hA : Measurable A) (y : Ω → ℝ) :
    (boundY1 μ A hi y - boundY0 μ A lo y) - (boundY1 μ A lo y - boundY0 μ A hi y) =
      (hi - lo) * μ.real univ := by
  rw [← measureReal_add_measureReal_compl (μ := μ) (measurableSet_treated hA)]
  simp only [boundY1, boundY0]
  ring

/-- For a probability measure, the upper endpoint minus the lower endpoint of the no-assumption
bounds on the average treatment effect is exactly `hi - lo`, whatever the observed data. As in
`ate_bounds_width_finite`, the identity also holds when `hi < lo`; it is the width of a genuine
interval only when `lo ≤ hi`. -/
theorem ate_bounds_width [IsProbabilityMeasure μ] (hA : Measurable A) (y : Ω → ℝ) :
    (boundY1 μ A hi y - boundY0 μ A lo y) - (boundY1 μ A lo y - boundY0 μ A hi y) = hi - lo := by
  rw [ate_bounds_width_finite hA, probReal_univ, mul_one]

/-- The model that agrees with the observed outcome `y` where it is observed and is filled with
`g1` (for `Y1` on `{A = 0}`) and `g0` (for `Y0` on `{A = 1}`) where it is not. -/
def fill (A : Ω → Bool) (y g1 g0 : Ω → ℝ) : POModel Ω where
  Y1 ω := if A ω then y ω else g1 ω
  Y0 ω := if A ω then g0 ω else y ω

omit [MeasurableSpace Ω] in
@[simp]
theorem observed_fill (y g1 g0 : Ω → ℝ) : observed A (fill A y g1 g0) = y := by
  funext ω
  simp only [observed, fill]
  cases A ω <;> rfl

theorem fill_mem_boundedModels (hA : Measurable A) {y g1 g0 : Ω → ℝ} (hy : Measurable y)
    (hg1 : Measurable g1) (hg0 : Measurable g0) (hyb : ∀ ω, y ω ∈ Icc lo hi)
    (hg1b : ∀ ω, g1 ω ∈ Icc lo hi) (hg0b : ∀ ω, g0 ω ∈ Icc lo hi) :
    fill A y g1 g0 ∈ boundedModels lo hi := by
  refine ⟨Measurable.ite (measurableSet_treated hA) hy hg1,
    Measurable.ite (measurableSet_treated hA) hg0 hy, fun ω => ?_, fun ω => ?_⟩ <;>
  · simp only [fill]
    split_ifs
    · first | exact hyb ω | exact hg0b ω
    · first | exact hg1b ω | exact hyb ω

theorem meanY1_fill [IsFiniteMeasure μ] (hA : Measurable A) {y g1 g0 : Ω → ℝ}
    (hm : fill A y g1 g0 ∈ boundedModels lo hi) :
    meanY1 μ (fill A y g1 g0) = ∫ ω in treated A, y ω ∂μ + ∫ ω in (treated A)ᶜ, g1 ω ∂μ := by
  have hS := measurableSet_treated hA
  rw [meanY1, ← integral_add_compl hS (integrable_of_mem_Icc hm.1 hm.2.2.1)]
  congr 1
  · exact setIntegral_congr_fun hS fun ω hω => by simp [fill, show A ω = true from hω]
  · exact setIntegral_congr_fun hS.compl fun ω hω => by
      simp [fill, show A ω = false by simpa [treated] using hω]

theorem meanY0_fill [IsFiniteMeasure μ] (hA : Measurable A) {y g1 g0 : Ω → ℝ}
    (hm : fill A y g1 g0 ∈ boundedModels lo hi) :
    meanY0 μ (fill A y g1 g0) = ∫ ω in treated A, g0 ω ∂μ + ∫ ω in (treated A)ᶜ, y ω ∂μ := by
  have hS := measurableSet_treated hA
  rw [meanY0, ← integral_add_compl hS (integrable_of_mem_Icc hm.2.1 hm.2.2.2)]
  congr 1
  · exact setIntegral_congr_fun hS fun ω hω => by simp [fill, show A ω = true from hω]
  · exact setIntegral_congr_fun hS.compl fun ω hω => by
      simp [fill, show A ω = false by simpa [treated] using hω]

/-- Every point of `Icc u v` is a convex combination of `u` and `v`; no order between `u` and
`v` is needed. -/
theorem exists_combo_of_mem_Icc {u v t : ℝ} (ht : t ∈ Icc u v) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * u + b * v = t := by
  have : t ∈ segment ℝ u v := by
    rw [segment_eq_Icc']
    exact Icc_subset_Icc (min_le_left _ _) (le_max_right _ _) ht
  obtain ⟨a, b, ha, hb, hab, h⟩ := this
  exact ⟨a, b, ha, hb, hab, by simpa using h⟩

/-- A convex combination of `lo ≤ hi` lies in `[lo, hi]`. -/
theorem combo_mem_Icc {a b lo hi : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hlh : lo ≤ hi) : a * lo + b * hi ∈ Icc lo hi := by
  have h1 := mul_nonneg ha (sub_nonneg.2 hlh)
  have h2 := mul_nonneg hb (sub_nonneg.2 hlh)
  have e1 : a * lo + b * hi = lo + b * (hi - lo) := by linear_combination lo * hab
  have e2 : a * lo + b * hi = hi - a * (hi - lo) := by linear_combination hi * hab
  constructor <;> linarith

/-- Sharpness of the bounds on `∫ Y1 dμ`, by explicit construction: for observed data `y`
(measurable with values in `[lo, hi]`) and every `t` between the lower and the upper bound,
there is a bounded model with the same observed outcome `y` and `∫ Y1 dμ = t`. Its `Y1` equals
`y` on `{A = 1}` and a suitable constant in `[lo, hi]` on `{A = 0}`. -/
theorem exists_model_meanY1_eq [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) {t : ℝ}
    (ht : t ∈ Icc (boundY1 μ A lo y) (boundY1 μ A hi y)) :
    ∃ m ∈ boundedModels lo hi, observed A m = y ∧ meanY1 μ m = t := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_combo_of_mem_Icc ht
  have hc : ∀ ω : Ω, a * lo + b * hi ∈ Icc lo hi := fun ω =>
    combo_mem_Icc ha hb hab ((hyb ω).1.trans (hyb ω).2)
  have hm := fill_mem_boundedModels hA hy measurable_const measurable_const hyb hc hc
    (g1 := fun _ => a * lo + b * hi) (g0 := fun _ => a * lo + b * hi)
  refine ⟨_, hm, observed_fill _ _ _, ?_⟩
  rw [meanY1_fill hA hm, setIntegral_const, smul_eq_mul, boundY1, boundY1]
  linear_combination (∫ ω in treated A, y ω ∂μ) * hab.symm

/-- The identified set for `∫ Y1 dμ` under bounded outcomes alone is exactly the Manski
interval. The observation is the realized outcome function `ω ↦ Y ω` on the fixed finite
measure space `(Ω, μ)` with the fixed treatment `A`; models differ only in their potential
outcomes. -/
theorem identifiedSet_meanY1 [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) :
    identifiedSet (boundedModels lo hi) (observed A) (meanY1 μ) y =
      Icc (boundY1 μ A lo y) (boundY1 μ A hi y) := by
  ext t
  constructor
  · rintro ⟨m, ⟨hm, rfl⟩, rfl⟩
    exact meanY1_mem_Icc hA hm
  · intro ht
    obtain ⟨m, hm, hobs, rfl⟩ := exists_model_meanY1_eq hA hy hyb ht
    exact mem_identifiedSet.2 ⟨m, hm, hobs, rfl⟩

/-- Sharpness of the bounds on `∫ Y0 dμ`, by explicit construction: every `t` between the lower
and the upper bound is `∫ Y0 dμ` of a bounded model with observed outcome `y`. Its `Y0` equals
`y` on `{A = 0}` and a suitable constant in `[lo, hi]` on `{A = 1}`. -/
theorem exists_model_meanY0_eq [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) {t : ℝ}
    (ht : t ∈ Icc (boundY0 μ A lo y) (boundY0 μ A hi y)) :
    ∃ m ∈ boundedModels lo hi, observed A m = y ∧ meanY0 μ m = t := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_combo_of_mem_Icc ht
  have hc : ∀ ω : Ω, a * lo + b * hi ∈ Icc lo hi := fun ω =>
    combo_mem_Icc ha hb hab ((hyb ω).1.trans (hyb ω).2)
  have hm := fill_mem_boundedModels hA hy measurable_const measurable_const hyb hc hc
    (g1 := fun _ => a * lo + b * hi) (g0 := fun _ => a * lo + b * hi)
  refine ⟨_, hm, observed_fill _ _ _, ?_⟩
  rw [meanY0_fill hA hm, setIntegral_const, smul_eq_mul, boundY0, boundY0]
  linear_combination (∫ ω in (treated A)ᶜ, y ω ∂μ) * hab.symm

/-- The identified set for `∫ Y0 dμ` under bounded outcomes alone is exactly the Manski interval,
with the same observation as in `identifiedSet_meanY1`. -/
theorem identifiedSet_meanY0 [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) :
    identifiedSet (boundedModels lo hi) (observed A) (meanY0 μ) y =
      Icc (boundY0 μ A lo y) (boundY0 μ A hi y) := by
  ext t
  constructor
  · rintro ⟨m, ⟨hm, rfl⟩, rfl⟩
    exact meanY0_mem_Icc hA hm
  · intro ht
    obtain ⟨m, hm, hobs, rfl⟩ := exists_model_meanY0_eq hA hy hyb ht
    exact mem_identifiedSet.2 ⟨m, hm, hobs, rfl⟩

/-- Sharpness of the bounds on the integrated treatment effect, by explicit construction:
every value between `boundY1 lo - boundY0 hi` and `boundY1 hi - boundY0 lo` is the integrated
treatment effect of a bounded model with observed outcome `y`. -/
theorem exists_model_ate_eq [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) {t : ℝ}
    (ht : t ∈ Icc (boundY1 μ A lo y - boundY0 μ A hi y) (boundY1 μ A hi y - boundY0 μ A lo y)) :
    ∃ m ∈ boundedModels lo hi, observed A m = y ∧ ate μ m = t := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_combo_of_mem_Icc ht
  have hc1 : ∀ ω : Ω, a * lo + b * hi ∈ Icc lo hi := fun ω =>
    combo_mem_Icc ha hb hab ((hyb ω).1.trans (hyb ω).2)
  have hc0 : ∀ ω : Ω, b * lo + a * hi ∈ Icc lo hi := fun ω =>
    combo_mem_Icc hb ha (by rw [add_comm, hab]) ((hyb ω).1.trans (hyb ω).2)
  have hm := fill_mem_boundedModels hA hy measurable_const measurable_const hyb hc1 hc0
    (g1 := fun _ => a * lo + b * hi) (g0 := fun _ => b * lo + a * hi)
  refine ⟨_, hm, observed_fill _ _ _, ?_⟩
  rw [ate, meanY1_fill hA hm, meanY0_fill hA hm, setIntegral_const, setIntegral_const,
    smul_eq_mul, smul_eq_mul, boundY1, boundY1, boundY0, boundY0]
  linear_combination
    (∫ ω in treated A, y ω ∂μ - ∫ ω in (treated A)ᶜ, y ω ∂μ) * hab.symm

/-- The identified set for the integrated treatment effect under bounded outcomes alone is
exactly the Manski interval. For the finite measure `μ` its endpoints differ by
`(hi - lo) * μ(Ω)` (see `ate_bounds_width_finite`); this is `hi - lo` only when `μ` is a
probability measure (see `ate_bounds_width`). The observation is the realized outcome function
on the fixed `(Ω, μ)` with the fixed treatment `A`. -/
theorem identifiedSet_ate [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) :
    identifiedSet (boundedModels lo hi) (observed A) (ate μ) y =
      Icc (boundY1 μ A lo y - boundY0 μ A hi y) (boundY1 μ A hi y - boundY0 μ A lo y) := by
  ext t
  constructor
  · rintro ⟨m, ⟨hm, rfl⟩, rfl⟩
    exact ate_mem_Icc hA hm
  · intro ht
    obtain ⟨m, hm, hobs, rfl⟩ := exists_model_ate_eq hA hy hyb ht
    exact mem_identifiedSet.2 ⟨m, hm, hobs, rfl⟩

/-- Non-identification of `∫ Y1 dμ` at every admissible observation: if the control group has
positive mass and `lo < hi`, the identified set at the observed outcome `y` contains at least
two points (both endpoints of the Manski interval). -/
theorem not_subsingleton_identifiedSet_meanY1 [IsFiniteMeasure μ] (hA : Measurable A)
    {y : Ω → ℝ} (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) (hlh : lo < hi)
    (hpos : 0 < μ.real (treated A)ᶜ) :
    ¬ (identifiedSet (boundedModels lo hi) (observed A) (meanY1 μ) y).Subsingleton := by
  have hlt : boundY1 μ A lo y < boundY1 μ A hi y := by unfold boundY1; gcongr
  rw [identifiedSet_meanY1 hA hy hyb]
  exact fun h => hlt.ne (h ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩)

/-- Non-identification of `∫ Y1 dμ` under bounded outcomes alone: if the control group has
positive mass and `lo < hi`, two bounded models with the same observed outcome have different
values of `∫ Y1 dμ`. The witness observation is the constant outcome `lo`. -/
theorem not_pointIdentified_meanY1 [IsFiniteMeasure μ] (hA : Measurable A) (hlh : lo < hi)
    (hpos : 0 < μ.real (treated A)ᶜ) :
    ¬ PointIdentified (boundedModels lo hi) (observed A) (meanY1 μ) := fun h =>
  not_subsingleton_identifiedSet_meanY1 (y := fun _ => lo) hA measurable_const
    (fun _ => ⟨le_rfl, hlh.le⟩) hlh hpos (pointIdentified_iff_subsingleton.1 h _)

/-- Zero lies in the no-assumption bounds on the integrated treatment effect, for any
admissible observed outcome: the model with `Y1 = Y0 = y` has effect zero. -/
theorem zero_mem_ate_bounds [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) :
    (0 : ℝ) ∈ Icc (boundY1 μ A lo y - boundY0 μ A hi y) (boundY1 μ A hi y - boundY0 μ A lo y) := by
  have hm := fill_mem_boundedModels hA hy hy hy hyb hyb hyb
  have h := ate_mem_Icc (μ := μ) hA hm
  have h0 : ate μ (fill A y y y) = 0 := by
    have e1 : (fill A y y y).Y1 = y := by funext ω; simp [fill]
    have e0 : (fill A y y y).Y0 = y := by funext ω; simp [fill]
    simp [ate, meanY1, meanY0, e1, e0]
  rwa [observed_fill, h0] at h

/-- The no-assumption lower bound on the integrated treatment effect is never positive, for any
admissible observed outcome. -/
theorem boundY1_lo_sub_boundY0_hi_nonpos [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) :
    boundY1 μ A lo y - boundY0 μ A hi y ≤ 0 :=
  (zero_mem_ate_bounds hA hy hyb).1

/-- The no-assumption upper bound on the integrated treatment effect is never negative, for any
admissible observed outcome. -/
theorem zero_le_boundY1_hi_sub_boundY0_lo [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) :
    0 ≤ boundY1 μ A hi y - boundY0 μ A lo y :=
  (zero_mem_ate_bounds hA hy hyb).2

/-- Non-identification of the integrated treatment effect at every admissible observation: if
`lo < hi` and `μ` has positive total mass, the identified set at `y` contains at least two
points, because its endpoints differ by `(hi - lo) * μ(Ω) > 0`. -/
theorem not_subsingleton_identifiedSet_ate [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) (hlh : lo < hi) (hpos : 0 < μ.real univ) :
    ¬ (identifiedSet (boundedModels lo hi) (observed A) (ate μ) y).Subsingleton := by
  have hw := ate_bounds_width_finite (μ := μ) (lo := lo) (hi := hi) hA y
  have hlt : boundY1 μ A lo y - boundY0 μ A hi y < boundY1 μ A hi y - boundY0 μ A lo y := by
    nlinarith [mul_pos (sub_pos.2 hlh) hpos]
  rw [identifiedSet_ate hA hy hyb]
  exact fun h => hlt.ne (h ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩)

/-- The average treatment effect is not point identified under bounded outcomes alone, for a
probability measure and `lo < hi`: the bounds have width `hi - lo > 0`. The witness observation
is the constant outcome `lo`. -/
theorem not_pointIdentified_ate [IsProbabilityMeasure μ] (hA : Measurable A) (hlh : lo < hi) :
    ¬ PointIdentified (boundedModels lo hi) (observed A) (ate μ) := fun h =>
  not_subsingleton_identifiedSet_ate (y := fun _ => lo) hA measurable_const
    (fun _ => ⟨le_rfl, hlh.le⟩) hlh (by simp) (pointIdentified_iff_subsingleton.1 h _)

/-- The sign of the integrated treatment effect is not identified at any admissible observation
without assumptions beyond bounded outcomes: if `lo < hi` and `μ` has positive total mass, the
identified set of `sign (ate)` at `y` contains `0` and a nonzero sign. Whether both a positive
and a negative sign occur depends on `y`; for example, `y = hi` on the treated and `y = lo` on
the controls gives lower endpoint `0`. -/
theorem not_subsingleton_identifiedSet_sign_ate [IsFiniteMeasure μ] (hA : Measurable A)
    {y : Ω → ℝ} (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) (hlh : lo < hi)
    (hpos : 0 < μ.real univ) :
    ¬ (identifiedSet (boundedModels lo hi) (observed A) (fun m => SignType.sign (ate μ m))
      y).Subsingleton := by
  have hw := ate_bounds_width_finite (μ := μ) (lo := lo) (hi := hi) hA y
  have hz := zero_mem_ate_bounds (μ := μ) hA hy hyb
  have hlt : boundY1 μ A lo y - boundY0 μ A hi y < boundY1 μ A hi y - boundY0 μ A lo y := by
    nlinarith [mul_pos (sub_pos.2 hlh) hpos]
  change ¬ (identifiedSet _ _ (SignType.sign ∘ ate μ) y).Subsingleton
  rw [identifiedSet_comp_param, identifiedSet_ate hA hy hyb]
  intro h
  have h0 : SignType.sign (0 : ℝ) ∈ SignType.sign '' Icc (boundY1 μ A lo y - boundY0 μ A hi y)
      (boundY1 μ A hi y - boundY0 μ A lo y) := mem_image_of_mem _ hz
  rcases hz.2.lt_or_eq with hU | hU
  · have := h h0 (mem_image_of_mem _ (right_mem_Icc.2 hlt.le))
    rw [sign_zero, sign_pos hU] at this
    exact absurd this (by decide)
  · have hL : boundY1 μ A lo y - boundY0 μ A hi y < 0 := hU ▸ hlt
    have := h h0 (mem_image_of_mem _ (left_mem_Icc.2 hlt.le))
    rw [sign_zero, sign_neg hL] at this
    exact absurd this (by decide)

/-- The sign of the average treatment effect is not point identified under bounded outcomes
alone, for a probability measure and `lo < hi`. -/
theorem not_pointIdentified_sign_ate [IsProbabilityMeasure μ] (hA : Measurable A)
    (hlh : lo < hi) :
    ¬ PointIdentified (boundedModels lo hi) (observed A) (fun m => SignType.sign (ate μ m)) :=
  fun h => not_subsingleton_identifiedSet_sign_ate (y := fun _ => lo) hA measurable_const
    (fun _ => ⟨le_rfl, hlh.le⟩) hlh (by simp) (pointIdentified_iff_subsingleton.1 h _)

/-! ### Monotone treatment response -/

/-- Under monotone treatment response (`Y0 ≤ Y1` pointwise) the integrated treatment effect is
nonnegative. -/
theorem ate_nonneg_of_mem_mtrModels [IsFiniteMeasure μ] {m : POModel Ω}
    (hm : m ∈ mtrModels lo hi) : 0 ≤ ate μ m := by
  have h : ∫ ω, m.Y0 ω ∂μ ≤ ∫ ω, m.Y1 ω ∂μ :=
    integral_mono (integrable_of_mem_Icc hm.1.2.1 hm.1.2.2.2)
      (integrable_of_mem_Icc hm.1.1 hm.1.2.2.1) hm.2
  simpa [ate, meanY1, meanY0] using h

/-- Bounds on the integrated treatment effect under monotone treatment response and bounded
outcomes (Manski 1997): the lower bound improves to `0`; the upper bound is the no-assumption
upper bound `boundY1 hi - boundY0 lo`. -/
theorem ate_mem_Icc_of_mem_mtrModels [IsFiniteMeasure μ] (hA : Measurable A) {m : POModel Ω}
    (hm : m ∈ mtrModels lo hi) :
    ate μ m ∈ Icc 0 (boundY1 μ A hi (observed A m) - boundY0 μ A lo (observed A m)) :=
  ⟨ate_nonneg_of_mem_mtrModels hm, (ate_mem_Icc hA hm.1).2⟩

/-- Sharpness of the monotone treatment response bounds, by explicit construction: every value
between `0` and `boundY1 hi - boundY0 lo` is the integrated treatment effect of a bounded model
satisfying monotone treatment response with observed outcome `y`. The model fills `Y1` on
`{A = 0}` with `a y + b hi` and `Y0` on `{A = 1}` with `b lo + a y`. -/
theorem exists_mtr_model_ate_eq [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) {t : ℝ}
    (ht : t ∈ Icc 0 (boundY1 μ A hi y - boundY0 μ A lo y)) :
    ∃ m ∈ mtrModels lo hi, observed A m = y ∧ ate μ m = t := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_combo_of_mem_Icc ht
  have hc1 : ∀ ω, a * y ω + b * hi ∈ Icc (y ω) hi := fun ω => combo_mem_Icc ha hb hab (hyb ω).2
  have hc0 : ∀ ω, b * lo + a * y ω ∈ Icc lo (y ω) := fun ω =>
    combo_mem_Icc hb ha (by rw [add_comm, hab]) (hyb ω).1
  have hm := fill_mem_boundedModels hA hy (g1 := fun ω => a * y ω + b * hi)
    (g0 := fun ω => b * lo + a * y ω) ((hy.const_mul a).add_const _)
    ((hy.const_mul a).const_add _) hyb (fun ω => ⟨(hyb ω).1.trans (hc1 ω).1, (hc1 ω).2⟩)
    (fun ω => ⟨(hc0 ω).1, (hc0 ω).2.trans (hyb ω).2⟩)
  have hmtr : fill A y (fun ω => a * y ω + b * hi) (fun ω => b * lo + a * y ω) ∈
      mtrModels lo hi := by
    refine ⟨hm, fun ω => ?_⟩
    simp only [fill]
    split_ifs
    · exact (hc0 ω).2
    · exact (hc1 ω).1
  refine ⟨_, hmtr, observed_fill _ _ _, ?_⟩
  have hyi : Integrable y μ := integrable_of_mem_Icc hy hyb
  have i1 : ∫ ω in (treated A)ᶜ, a * y ω + b * hi ∂μ =
      a * ∫ ω in (treated A)ᶜ, y ω ∂μ + μ.real (treated A)ᶜ * (b * hi) := by
    rw [integral_add (hyi.integrableOn.const_mul a) (integrable_const _), integral_const_mul a,
      setIntegral_const, smul_eq_mul]
  have i0 : ∫ ω in treated A, b * lo + a * y ω ∂μ =
      μ.real (treated A) * (b * lo) + a * ∫ ω in treated A, y ω ∂μ := by
    rw [integral_add (integrable_const _) (hyi.integrableOn.const_mul a), integral_const_mul a,
      setIntegral_const, smul_eq_mul]
  rw [ate, meanY1_fill hA hm, meanY0_fill hA hm, i1, i0, boundY1, boundY0]
  linear_combination
    (∫ ω in treated A, y ω ∂μ - ∫ ω in (treated A)ᶜ, y ω ∂μ) * hab.symm

/-- The identified set for the integrated treatment effect under monotone treatment response and
bounded outcomes is exactly `[0, boundY1 hi - boundY0 lo]`. Compared with `identifiedSet_ate`,
the lower endpoint moves up from `boundY1 lo - boundY0 hi ≤ 0` to `0` and the upper endpoint
is unchanged. The observation is the realized outcome function on the fixed `(Ω, μ)` with the
fixed treatment `A`. -/
theorem identifiedSet_ate_mtr [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) :
    identifiedSet (mtrModels lo hi) (observed A) (ate μ) y =
      Icc 0 (boundY1 μ A hi y - boundY0 μ A lo y) := by
  ext t
  constructor
  · rintro ⟨m, ⟨hm, rfl⟩, rfl⟩
    exact ate_mem_Icc_of_mem_mtrModels hA hm
  · intro ht
    obtain ⟨m, hm, hobs, rfl⟩ := exists_mtr_model_ate_eq hA hy hyb ht
    exact mem_identifiedSet.2 ⟨m, hm, hobs, rfl⟩

/-- The observed outcome of a bounded model is measurable with values in `[lo, hi]`. -/
theorem observed_measurable_mem_Icc (hA : Measurable A) {m : POModel Ω}
    (hm : m ∈ boundedModels lo hi) :
    Measurable (observed A m) ∧ ∀ ω, observed A m ω ∈ Icc lo hi := by
  refine ⟨Measurable.ite (measurableSet_treated hA) hm.1 hm.2.1, fun ω => ?_⟩
  simp only [observed]
  split_ifs
  · exact hm.2.2.1 ω
  · exact hm.2.2.2 ω

/-- Bounds on `∫ Y1 dμ` under monotone treatment response and bounded outcomes (Manski 1997):
`∫ Y dμ ≤ ∫ Y1 dμ ≤ boundY1 hi`. The lower bound improves from `boundY1 lo` to the integral of
the observed outcome, since `Y1 ≥ Y0 = Y` on the controls. -/
theorem meanY1_mem_Icc_of_mem_mtrModels [IsFiniteMeasure μ] (hA : Measurable A)
    {m : POModel Ω} (hm : m ∈ mtrModels lo hi) :
    meanY1 μ m ∈ Icc (∫ ω, observed A m ω ∂μ) (boundY1 μ A hi (observed A m)) := by
  obtain ⟨hyo, hyob⟩ := observed_measurable_mem_Icc hA hm.1
  refine ⟨integral_mono (integrable_of_mem_Icc hyo hyob)
    (integrable_of_mem_Icc hm.1.1 hm.1.2.2.1) fun ω => ?_, (meanY1_mem_Icc hA hm.1).2⟩
  simp only [observed]
  split_ifs
  · exact le_rfl
  · exact hm.2 ω

/-- Bounds on `∫ Y0 dμ` under monotone treatment response and bounded outcomes (Manski 1997):
`boundY0 lo ≤ ∫ Y0 dμ ≤ ∫ Y dμ`. The upper bound improves from `boundY0 hi` to the integral of
the observed outcome, since `Y0 ≤ Y1 = Y` on the treated. -/
theorem meanY0_mem_Icc_of_mem_mtrModels [IsFiniteMeasure μ] (hA : Measurable A)
    {m : POModel Ω} (hm : m ∈ mtrModels lo hi) :
    meanY0 μ m ∈ Icc (boundY0 μ A lo (observed A m)) (∫ ω, observed A m ω ∂μ) := by
  obtain ⟨hyo, hyob⟩ := observed_measurable_mem_Icc hA hm.1
  refine ⟨(meanY0_mem_Icc hA hm.1).1, integral_mono (integrable_of_mem_Icc hm.1.2.1 hm.1.2.2.2)
    (integrable_of_mem_Icc hyo hyob) fun ω => ?_⟩
  simp only [observed]
  split_ifs
  · exact hm.2 ω
  · exact le_rfl

/-- Sharpness of the monotone treatment response bounds on `∫ Y1 dμ`, by explicit construction:
every value between `∫ y dμ` and `boundY1 hi y` is `∫ Y1 dμ` of a bounded model satisfying
monotone treatment response with observed outcome `y`. The model fills `Y1` on `{A = 0}` with
`a y + b hi` and `Y0` on `{A = 1}` with `y`. -/
theorem exists_mtr_model_meanY1_eq [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) {t : ℝ}
    (ht : t ∈ Icc (∫ ω, y ω ∂μ) (boundY1 μ A hi y)) :
    ∃ m ∈ mtrModels lo hi, observed A m = y ∧ meanY1 μ m = t := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_combo_of_mem_Icc ht
  have hc1 : ∀ ω, a * y ω + b * hi ∈ Icc (y ω) hi := fun ω => combo_mem_Icc ha hb hab (hyb ω).2
  have hm := fill_mem_boundedModels hA hy (g1 := fun ω => a * y ω + b * hi) (g0 := y)
    ((hy.const_mul a).add_const _) hy hyb (fun ω => ⟨(hyb ω).1.trans (hc1 ω).1, (hc1 ω).2⟩) hyb
  have hmtr : fill A y (fun ω => a * y ω + b * hi) y ∈ mtrModels lo hi := by
    refine ⟨hm, fun ω => ?_⟩
    simp only [fill]
    split_ifs
    · exact le_rfl
    · exact (hc1 ω).1
  refine ⟨_, hmtr, observed_fill _ _ _, ?_⟩
  have hS := measurableSet_treated hA
  have hyi : Integrable y μ := integrable_of_mem_Icc hy hyb
  have i1 : ∫ ω in (treated A)ᶜ, a * y ω + b * hi ∂μ =
      a * ∫ ω in (treated A)ᶜ, y ω ∂μ + μ.real (treated A)ᶜ * (b * hi) := by
    rw [integral_add (hyi.integrableOn.const_mul a) (integrable_const _), integral_const_mul a,
      setIntegral_const, smul_eq_mul]
  rw [meanY1_fill hA hm, i1, boundY1, ← integral_add_compl hS hyi]
  linear_combination (∫ ω in treated A, y ω ∂μ) * hab.symm

/-- Sharpness of the monotone treatment response bounds on `∫ Y0 dμ`, by explicit construction:
every value between `boundY0 lo y` and `∫ y dμ` is `∫ Y0 dμ` of a bounded model satisfying
monotone treatment response with observed outcome `y`. The model fills `Y1` on `{A = 0}` with
`y` and `Y0` on `{A = 1}` with `a lo + b y`. -/
theorem exists_mtr_model_meanY0_eq [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) {t : ℝ}
    (ht : t ∈ Icc (boundY0 μ A lo y) (∫ ω, y ω ∂μ)) :
    ∃ m ∈ mtrModels lo hi, observed A m = y ∧ meanY0 μ m = t := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := exists_combo_of_mem_Icc ht
  have hc0 : ∀ ω, a * lo + b * y ω ∈ Icc lo (y ω) := fun ω => combo_mem_Icc ha hb hab (hyb ω).1
  have hm := fill_mem_boundedModels hA hy (g1 := y) (g0 := fun ω => a * lo + b * y ω) hy
    ((hy.const_mul b).const_add _) hyb hyb (fun ω => ⟨(hc0 ω).1, (hc0 ω).2.trans (hyb ω).2⟩)
  have hmtr : fill A y y (fun ω => a * lo + b * y ω) ∈ mtrModels lo hi := by
    refine ⟨hm, fun ω => ?_⟩
    simp only [fill]
    split_ifs
    · exact (hc0 ω).2
    · exact le_rfl
  refine ⟨_, hmtr, observed_fill _ _ _, ?_⟩
  have hS := measurableSet_treated hA
  have hyi : Integrable y μ := integrable_of_mem_Icc hy hyb
  have i0 : ∫ ω in treated A, a * lo + b * y ω ∂μ =
      μ.real (treated A) * (a * lo) + b * ∫ ω in treated A, y ω ∂μ := by
    rw [integral_add (integrable_const _) (hyi.integrableOn.const_mul b), integral_const_mul b,
      setIntegral_const, smul_eq_mul]
  rw [meanY0_fill hA hm, i0, boundY0, ← integral_add_compl hS hyi]
  linear_combination (∫ ω in (treated A)ᶜ, y ω ∂μ) * hab.symm

/-- The identified set for `∫ Y1 dμ` under monotone treatment response and bounded outcomes is
exactly `[∫ y dμ, boundY1 hi y]`, with the realized outcome function as observation. -/
theorem identifiedSet_meanY1_mtr [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) :
    identifiedSet (mtrModels lo hi) (observed A) (meanY1 μ) y =
      Icc (∫ ω, y ω ∂μ) (boundY1 μ A hi y) := by
  ext t
  constructor
  · rintro ⟨m, ⟨hm, rfl⟩, rfl⟩
    exact meanY1_mem_Icc_of_mem_mtrModels hA hm
  · intro ht
    obtain ⟨m, hm, hobs, rfl⟩ := exists_mtr_model_meanY1_eq hA hy hyb ht
    exact mem_identifiedSet.2 ⟨m, hm, hobs, rfl⟩

/-- The identified set for `∫ Y0 dμ` under monotone treatment response and bounded outcomes is
exactly `[boundY0 lo y, ∫ y dμ]`, with the realized outcome function as observation. -/
theorem identifiedSet_meanY0_mtr [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) :
    identifiedSet (mtrModels lo hi) (observed A) (meanY0 μ) y =
      Icc (boundY0 μ A lo y) (∫ ω, y ω ∂μ) := by
  ext t
  constructor
  · rintro ⟨m, ⟨hm, rfl⟩, rfl⟩
    exact meanY0_mem_Icc_of_mem_mtrModels hA hm
  · intro ht
    obtain ⟨m, hm, hobs, rfl⟩ := exists_mtr_model_meanY0_eq hA hy hyb ht
    exact mem_identifiedSet.2 ⟨m, hm, hobs, rfl⟩

/-! ### Coarser observations: arm integrals and the joint law of `(A, Y)`

The identified sets above use the realized outcome function as observation. The bounds depend
on it only through the two observed arm integrals, so the same intervals are the identified sets
when only the arm integrals, or only the joint law of `(A, Y)`, are observed. The treatment `A`
and the measure `μ` stay fixed, so the arm masses `μ(A = 1)` and `μ(A = 0)` are known
constants. -/

/-- The observed arm integrals `(∫_{A = 1} y dμ, ∫_{A = 0} y dμ)` of an outcome function `y`. -/
noncomputable def armIntegrals (μ : Measure Ω) (A : Ω → Bool) (y : Ω → ℝ) : ℝ × ℝ :=
  (∫ ω in treated A, y ω ∂μ, ∫ ω in (treated A)ᶜ, y ω ∂μ)

/-- The joint law of `(A, y)` under `μ`, a measure on `Bool × ℝ`. -/
noncomputable def jointLaw (μ : Measure Ω) (A : Ω → Bool) (y : Ω → ℝ) : Measure (Bool × ℝ) :=
  μ.map fun ω => (A ω, y ω)

/-- The arm integral of a measure `L` on `Bool × ℝ`: the integral of the second coordinate over
the slice `{(a, v) | a = b}`. -/
noncomputable def lawArmIntegral (L : Measure (Bool × ℝ)) (b : Bool) : ℝ :=
  ∫ q in Prod.fst ⁻¹' {b}, q.2 ∂L

/-- The arm integral of the joint law of `(A, y)` on the slice `a = b` is the integral of `y`
over `{A = b}`. -/
theorem lawArmIntegral_jointLaw (hA : Measurable A) {y : Ω → ℝ} (hy : Measurable y)
    (b : Bool) :
    lawArmIntegral (jointLaw μ A y) b = ∫ ω in {ω | A ω = b}, y ω ∂μ := by
  rw [lawArmIntegral, jointLaw, setIntegral_map (measurable_fst (measurableSet_singleton b))
    measurable_snd.aestronglyMeasurable (hA.prodMk hy).aemeasurable]
  rfl

/-- The arm integral over `{A = 1}` is a functional of the joint law of `(A, y)`. -/
theorem lawArmIntegral_jointLaw_true (hA : Measurable A) {y : Ω → ℝ} (hy : Measurable y) :
    lawArmIntegral (jointLaw μ A y) true = ∫ ω in treated A, y ω ∂μ :=
  lawArmIntegral_jointLaw hA hy true

/-- The arm integral over `{A = 0}` is a functional of the joint law of `(A, y)`. -/
theorem lawArmIntegral_jointLaw_false (hA : Measurable A) {y : Ω → ℝ} (hy : Measurable y) :
    lawArmIntegral (jointLaw μ A y) false = ∫ ω in (treated A)ᶜ, y ω ∂μ := by
  rw [lawArmIntegral_jointLaw hA hy false]
  congr 2
  ext ω
  simp [treated]

/-- The identified set for `∫ Y1 dμ` under bounded outcomes alone, when the observation is the
pair of observed arm integrals: at every attainable value `p` it is
`[p.1 + lo μ(A = 0), p.1 + hi μ(A = 0)]`. -/
theorem identifiedSet_meanY1_armIntegrals [IsFiniteMeasure μ] (hA : Measurable A)
    {p : ℝ × ℝ} (hp : ∃ m ∈ boundedModels lo hi, armIntegrals μ A (observed A m) = p) :
    identifiedSet (boundedModels lo hi) (fun m => armIntegrals μ A (observed A m)) (meanY1 μ) p =
      Icc (p.1 + lo * μ.real (treated A)ᶜ) (p.1 + hi * μ.real (treated A)ᶜ) := by
  obtain ⟨m₀, hm₀, rfl⟩ := hp
  refine identifiedSet_comp_obs_eq (obs := observed A) (armIntegrals μ A)
    (fun p => Icc (p.1 + lo * μ.real (treated A)ᶜ) (p.1 + hi * μ.real (treated A)ᶜ))
    (fun m hm => ?_) hm₀
  obtain ⟨h1, h2⟩ := observed_measurable_mem_Icc hA hm
  exact identifiedSet_meanY1 hA h1 h2

/-- The identified set for `∫ Y0 dμ` under bounded outcomes alone, when the observation is the
pair of observed arm integrals: at every attainable value `p` it is
`[p.2 + lo μ(A = 1), p.2 + hi μ(A = 1)]`. -/
theorem identifiedSet_meanY0_armIntegrals [IsFiniteMeasure μ] (hA : Measurable A)
    {p : ℝ × ℝ} (hp : ∃ m ∈ boundedModels lo hi, armIntegrals μ A (observed A m) = p) :
    identifiedSet (boundedModels lo hi) (fun m => armIntegrals μ A (observed A m)) (meanY0 μ) p =
      Icc (p.2 + lo * μ.real (treated A)) (p.2 + hi * μ.real (treated A)) := by
  obtain ⟨m₀, hm₀, rfl⟩ := hp
  refine identifiedSet_comp_obs_eq (obs := observed A) (armIntegrals μ A)
    (fun p => Icc (p.2 + lo * μ.real (treated A)) (p.2 + hi * μ.real (treated A)))
    (fun m hm => ?_) hm₀
  obtain ⟨h1, h2⟩ := observed_measurable_mem_Icc hA hm
  exact identifiedSet_meanY0 hA h1 h2

/-- The identified set for the integrated treatment effect under bounded outcomes alone, when the
observation is the pair of observed arm integrals: at every attainable value `p` it is
`[p.1 + lo μ(A = 0) - (p.2 + hi μ(A = 1)), p.1 + hi μ(A = 0) - (p.2 + lo μ(A = 1))]`. -/
theorem identifiedSet_ate_armIntegrals [IsFiniteMeasure μ] (hA : Measurable A)
    {p : ℝ × ℝ} (hp : ∃ m ∈ boundedModels lo hi, armIntegrals μ A (observed A m) = p) :
    identifiedSet (boundedModels lo hi) (fun m => armIntegrals μ A (observed A m)) (ate μ) p =
      Icc (p.1 + lo * μ.real (treated A)ᶜ - (p.2 + hi * μ.real (treated A)))
        (p.1 + hi * μ.real (treated A)ᶜ - (p.2 + lo * μ.real (treated A))) := by
  obtain ⟨m₀, hm₀, rfl⟩ := hp
  refine identifiedSet_comp_obs_eq (obs := observed A) (armIntegrals μ A)
    (fun p => Icc (p.1 + lo * μ.real (treated A)ᶜ - (p.2 + hi * μ.real (treated A)))
      (p.1 + hi * μ.real (treated A)ᶜ - (p.2 + lo * μ.real (treated A))))
    (fun m hm => ?_) hm₀
  obtain ⟨h1, h2⟩ := observed_measurable_mem_Icc hA hm
  exact identifiedSet_ate hA h1 h2

/-- The identified set for `∫ Y1 dμ` under bounded outcomes alone, when the observation is the
joint law `L` of `(A, Y)`: at every attainable law it is
`[∫_{a = 1} v dL + lo μ(A = 0), ∫_{a = 1} v dL + hi μ(A = 0)]`. -/
theorem identifiedSet_meanY1_jointLaw [IsFiniteMeasure μ] (hA : Measurable A)
    {L : Measure (Bool × ℝ)} (hL : ∃ m ∈ boundedModels lo hi, jointLaw μ A (observed A m) = L) :
    identifiedSet (boundedModels lo hi) (fun m => jointLaw μ A (observed A m)) (meanY1 μ) L =
      Icc (lawArmIntegral L true + lo * μ.real (treated A)ᶜ)
        (lawArmIntegral L true + hi * μ.real (treated A)ᶜ) := by
  obtain ⟨m₀, hm₀, rfl⟩ := hL
  refine identifiedSet_comp_obs_eq (obs := observed A) (jointLaw μ A)
    (fun L => Icc (lawArmIntegral L true + lo * μ.real (treated A)ᶜ)
      (lawArmIntegral L true + hi * μ.real (treated A)ᶜ))
    (fun m hm => ?_) hm₀
  obtain ⟨h1, h2⟩ := observed_measurable_mem_Icc hA hm
  rw [identifiedSet_meanY1 hA h1 h2, lawArmIntegral_jointLaw_true hA h1, boundY1, boundY1]

/-- The identified set for `∫ Y0 dμ` under bounded outcomes alone, when the observation is the
joint law `L` of `(A, Y)`: at every attainable law it is
`[∫_{a = 0} v dL + lo μ(A = 1), ∫_{a = 0} v dL + hi μ(A = 1)]`. -/
theorem identifiedSet_meanY0_jointLaw [IsFiniteMeasure μ] (hA : Measurable A)
    {L : Measure (Bool × ℝ)} (hL : ∃ m ∈ boundedModels lo hi, jointLaw μ A (observed A m) = L) :
    identifiedSet (boundedModels lo hi) (fun m => jointLaw μ A (observed A m)) (meanY0 μ) L =
      Icc (lawArmIntegral L false + lo * μ.real (treated A))
        (lawArmIntegral L false + hi * μ.real (treated A)) := by
  obtain ⟨m₀, hm₀, rfl⟩ := hL
  refine identifiedSet_comp_obs_eq (obs := observed A) (jointLaw μ A)
    (fun L => Icc (lawArmIntegral L false + lo * μ.real (treated A))
      (lawArmIntegral L false + hi * μ.real (treated A)))
    (fun m hm => ?_) hm₀
  obtain ⟨h1, h2⟩ := observed_measurable_mem_Icc hA hm
  rw [identifiedSet_meanY0 hA h1 h2, lawArmIntegral_jointLaw_false hA h1, boundY0, boundY0]

/-- The identified set for the integrated treatment effect under bounded outcomes alone, when
the observation is the joint law `L` of `(A, Y)`: at every attainable law it is the Manski
interval with the arm integrals read off `L`. -/
theorem identifiedSet_ate_jointLaw [IsFiniteMeasure μ] (hA : Measurable A)
    {L : Measure (Bool × ℝ)} (hL : ∃ m ∈ boundedModels lo hi, jointLaw μ A (observed A m) = L) :
    identifiedSet (boundedModels lo hi) (fun m => jointLaw μ A (observed A m)) (ate μ) L =
      Icc (lawArmIntegral L true + lo * μ.real (treated A)ᶜ -
          (lawArmIntegral L false + hi * μ.real (treated A)))
        (lawArmIntegral L true + hi * μ.real (treated A)ᶜ -
          (lawArmIntegral L false + lo * μ.real (treated A))) := by
  obtain ⟨m₀, hm₀, rfl⟩ := hL
  refine identifiedSet_comp_obs_eq (obs := observed A) (jointLaw μ A)
    (fun L => Icc (lawArmIntegral L true + lo * μ.real (treated A)ᶜ -
          (lawArmIntegral L false + hi * μ.real (treated A)))
        (lawArmIntegral L true + hi * μ.real (treated A)ᶜ -
          (lawArmIntegral L false + lo * μ.real (treated A))))
    (fun m hm => ?_) hm₀
  obtain ⟨h1, h2⟩ := observed_measurable_mem_Icc hA hm
  rw [identifiedSet_ate hA h1 h2, lawArmIntegral_jointLaw_true hA h1,
    lawArmIntegral_jointLaw_false hA h1, boundY1, boundY1, boundY0, boundY0]

end Manski

end CausalInference
