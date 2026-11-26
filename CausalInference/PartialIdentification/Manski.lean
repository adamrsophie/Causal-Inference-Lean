/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import CausalInference.PartialIdentification.IdentifiedSet

/-!
# Manski bounds for a binary treatment with bounded outcomes

Worst-case (no-assumption) bounds on the mean potential outcomes and on the average treatment
effect, their sharpness by explicit construction, and the tightening of the lower bound under
monotone treatment response.

## Setting

Measure-theoretic. A measurable space `Ω` with a finite measure `μ` (a probability measure in
applications; only `ate_bounds_width` needs total mass one), a measurable binary treatment
`A : Ω → Bool`, and a potential outcome model `m : POModel Ω` with measurable potential outcomes
`m.Y1`, `m.Y0` taking values in `[lo, hi]`. The observed outcome is
`Y = if A then Y1 else Y0`.

For the identified set statements the observation is the realized outcome function
`observed A m : Ω → ℝ` on the fixed `(Ω, μ)` with the fixed treatment `A`; models vary only in
their potential outcomes. This observation is finer than the observed law of `(A, Y)`; the
bounds themselves are functionals of that law (a set integral of `Y` over `{A = 1}` or
`{A = 0}` and the treatment probabilities).

## Main results

* `meanY1_mem_Icc`, `meanY0_mem_Icc`: for every bounded model,
  `E[Y 1_{A=1}] + lo P(A=0) ≤ E[Y1] ≤ E[Y 1_{A=1}] + hi P(A=0)`, and similarly for `E[Y0]`.
* `ate_mem_Icc`: the resulting bounds on the average treatment effect, and
  `ate_bounds_width`: their width is exactly `hi - lo`.
* `exists_model_meanY1_eq`, `exists_model_meanY0_eq`, `exists_model_ate_eq`: sharpness by
  explicit construction.
* `identifiedSet_meanY1`, `identifiedSet_meanY0`, `identifiedSet_ate`: the identified sets (in
  the sense of `CausalInference.identifiedSet`) are exactly the closed intervals.
* `not_pointIdentified_meanY1`: `E[Y1]` is not point identified when `lo < hi` and
  `P(A=0) > 0`.
* `ate_mem_Icc_of_mem_mtrModels`, `exists_mtr_model_ate_eq`, `identifiedSet_ate_mtr`: under
  monotone treatment response the identified set for the average treatment effect is exactly
  `[0, boundY1 hi - boundY0 lo]`.

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

/-- The mean `E[Y1]` of the treated potential outcome. -/
noncomputable def meanY1 (μ : Measure Ω) (m : POModel Ω) : ℝ := ∫ ω, m.Y1 ω ∂μ

/-- The mean `E[Y0]` of the control potential outcome. -/
noncomputable def meanY0 (μ : Measure Ω) (m : POModel Ω) : ℝ := ∫ ω, m.Y0 ω ∂μ

/-- The average treatment effect `E[Y1] - E[Y0]`. -/
noncomputable def ate (μ : Measure Ω) (m : POModel Ω) : ℝ := meanY1 μ m - meanY0 μ m

/-- The Manski bound for `E[Y1]` with fill value `c`: `E[Y 1_{A=1}] + c P(A=0)`. With `c = lo`
it is the lower bound, with `c = hi` the upper bound. It depends only on observed data. -/
noncomputable def boundY1 (μ : Measure Ω) (A : Ω → Bool) (c : ℝ) (y : Ω → ℝ) : ℝ :=
  ∫ ω in treated A, y ω ∂μ + c * μ.real (treated A)ᶜ

/-- The Manski bound for `E[Y0]` with fill value `c`: `E[Y 1_{A=0}] + c P(A=1)`. -/
noncomputable def boundY0 (μ : Measure Ω) (A : Ω → Bool) (c : ℝ) (y : Ω → ℝ) : ℝ :=
  ∫ ω in (treated A)ᶜ, y ω ∂μ + c * μ.real (treated A)

variable {A : Ω → Bool} {lo hi : ℝ}

/-- No-assumption bounds on `E[Y1]` (Manski 1990): for every bounded model,
`E[Y 1_{A=1}] + lo P(A=0) ≤ E[Y1] ≤ E[Y 1_{A=1}] + hi P(A=0)`, where `Y` is the observed
outcome. -/
theorem meanY1_mem_Icc [IsFiniteMeasure μ] (hA : Measurable A) {m : POModel Ω}
    (hm : m ∈ boundedModels lo hi) :
    meanY1 μ m ∈ Icc (boundY1 μ A lo (observed A m)) (boundY1 μ A hi (observed A m)) :=
  integral_mem_Icc_of_eqOn (measurableSet_treated hA) hm.1 hm.2.2.1 fun ω hω => by
    simp [observed, show A ω = true from hω]

/-- No-assumption bounds on `E[Y0]`:
`E[Y 1_{A=0}] + lo P(A=1) ≤ E[Y0] ≤ E[Y 1_{A=0}] + hi P(A=1)`. -/
theorem meanY0_mem_Icc [IsFiniteMeasure μ] (hA : Measurable A) {m : POModel Ω}
    (hm : m ∈ boundedModels lo hi) :
    meanY0 μ m ∈ Icc (boundY0 μ A lo (observed A m)) (boundY0 μ A hi (observed A m)) := by
  have h := integral_mem_Icc_of_eqOn (μ := μ) (measurableSet_treated hA).compl hm.2.1 hm.2.2.2
    (y := observed A m) fun ω hω => by
      simp [observed, show A ω = false by simpa [treated] using hω]
  rwa [compl_compl] at h

/-- No-assumption bounds on the average treatment effect:
`boundY1 lo - boundY0 hi ≤ E[Y1] - E[Y0] ≤ boundY1 hi - boundY0 lo`. -/
theorem ate_mem_Icc [IsFiniteMeasure μ] (hA : Measurable A) {m : POModel Ω}
    (hm : m ∈ boundedModels lo hi) :
    ate μ m ∈ Icc (boundY1 μ A lo (observed A m) - boundY0 μ A hi (observed A m))
      (boundY1 μ A hi (observed A m) - boundY0 μ A lo (observed A m)) := by
  have h1 := meanY1_mem_Icc (μ := μ) hA hm
  have h0 := meanY0_mem_Icc (μ := μ) hA hm
  exact ⟨by unfold ate; linarith [h1.1, h0.2], by unfold ate; linarith [h1.2, h0.1]⟩

/-- The no-assumption bounds on the average treatment effect have width exactly `hi - lo`,
whatever the observed data. -/
theorem ate_bounds_width [IsProbabilityMeasure μ] (hA : Measurable A) (y : Ω → ℝ) :
    (boundY1 μ A hi y - boundY0 μ A lo y) - (boundY1 μ A lo y - boundY0 μ A hi y) = hi - lo := by
  have h := probReal_compl_eq_one_sub (μ := μ) (measurableSet_treated hA)
  simp only [boundY1, boundY0, h]
  ring

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

/-- Sharpness of the bounds on `E[Y1]`, by explicit construction: for observed data `y`
(measurable with values in `[lo, hi]`) and every `t` between the lower and the upper bound,
there is a bounded model with the same observed outcome `y` and `E[Y1] = t`. Its `Y1` equals
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

/-- The identified set for `E[Y1]` under bounded outcomes alone is exactly the Manski interval.
The observation is the realized outcome function `ω ↦ Y ω` on the fixed probability space
`(Ω, μ)` with the fixed treatment `A`; models differ only in their potential outcomes. -/
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

/-- Sharpness of the bounds on `E[Y0]`, by explicit construction: every `t` between the lower
and the upper bound is `E[Y0]` of a bounded model with observed outcome `y`. Its `Y0` equals
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

/-- The identified set for `E[Y0]` under bounded outcomes alone is exactly the Manski interval,
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

/-- Sharpness of the bounds on the average treatment effect, by explicit construction: every
value between `boundY1 lo - boundY0 hi` and `boundY1 hi - boundY0 lo` is the average treatment
effect of a bounded model with observed outcome `y`. -/
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

/-- The identified set for the average treatment effect under bounded outcomes alone is exactly
the Manski interval, of width `hi - lo` (see `ate_bounds_width`). The observation is the
realized outcome function on the fixed `(Ω, μ)` with the fixed treatment `A`. -/
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

/-- Non-identification of `E[Y1]` under bounded outcomes alone: if the control group has
positive probability and `lo < hi`, two bounded models with the same observed outcome have
different means `E[Y1]`. -/
theorem not_pointIdentified_meanY1 [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) (hlh : lo < hi)
    (hpos : 0 < μ.real (treated A)ᶜ) :
    ¬ PointIdentified (boundedModels lo hi) (observed A) (meanY1 μ) := by
  have hle : boundY1 μ A lo y ≤ boundY1 μ A hi y := by
    unfold boundY1; gcongr
  refine not_pointIdentified_of_mem (o := y) ?_ ?_ (ne_of_lt (show
    boundY1 μ A lo y < boundY1 μ A hi y by unfold boundY1; gcongr))
  · rw [identifiedSet_meanY1 hA hy hyb]; exact ⟨le_rfl, hle⟩
  · rw [identifiedSet_meanY1 hA hy hyb]; exact ⟨hle, le_rfl⟩

/-- The no-assumption lower bound on the average treatment effect is never positive, for any
admissible observed outcome. -/
theorem boundY1_lo_sub_boundY0_hi_nonpos [IsFiniteMeasure μ] (hA : Measurable A) {y : Ω → ℝ}
    (hy : Measurable y) (hyb : ∀ ω, y ω ∈ Icc lo hi) :
    boundY1 μ A lo y - boundY0 μ A hi y ≤ 0 := by
  have hm := fill_mem_boundedModels hA hy hy hy hyb hyb hyb
  have h := (ate_mem_Icc (μ := μ) hA hm).1
  have h0 : ate μ (fill A y y y) = 0 := by
    have e1 : (fill A y y y).Y1 = y := by funext ω; simp [fill]
    have e0 : (fill A y y y).Y0 = y := by funext ω; simp [fill]
    simp [ate, meanY1, meanY0, e1, e0]
  rwa [observed_fill, h0] at h

/-! ### Monotone treatment response -/

/-- Under monotone treatment response (`Y0 ≤ Y1` pointwise) the average treatment effect is
nonnegative. -/
theorem ate_nonneg_of_mem_mtrModels [IsFiniteMeasure μ] {m : POModel Ω}
    (hm : m ∈ mtrModels lo hi) : 0 ≤ ate μ m := by
  have h : ∫ ω, m.Y0 ω ∂μ ≤ ∫ ω, m.Y1 ω ∂μ :=
    integral_mono (integrable_of_mem_Icc hm.1.2.1 hm.1.2.2.2)
      (integrable_of_mem_Icc hm.1.1 hm.1.2.2.1) hm.2
  simpa [ate, meanY1, meanY0] using h

/-- Bounds on the average treatment effect under monotone treatment response and bounded
outcomes (Manski 1997): the lower bound improves to `0`; the upper bound is the no-assumption
upper bound `boundY1 hi - boundY0 lo`. -/
theorem ate_mem_Icc_of_mem_mtrModels [IsFiniteMeasure μ] (hA : Measurable A) {m : POModel Ω}
    (hm : m ∈ mtrModels lo hi) :
    ate μ m ∈ Icc 0 (boundY1 μ A hi (observed A m) - boundY0 μ A lo (observed A m)) :=
  ⟨ate_nonneg_of_mem_mtrModels hm, (ate_mem_Icc hA hm.1).2⟩

/-- Sharpness of the monotone treatment response bounds, by explicit construction: every value
between `0` and `boundY1 hi - boundY0 lo` is the average treatment effect of a bounded model
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

/-- The identified set for the average treatment effect under monotone treatment response and
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

end Manski

end CausalInference
