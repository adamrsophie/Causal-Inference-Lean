/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.ConvergenceInProbability
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Total variation bounds and the Bernstein and von Mises predicates

The total variation distance is Mathlib's `MeasureTheory.tvDist`. With Mathlib's convention it
is `‖μ - ν‖`, the total variation norm of the signed measure `μ - ν`: for probability measures it
takes values in `[0, 2]` and equals twice `sup_A |μ A - ν A|`. This file adds the bounds that the
posterior limit theory uses, proved from a Hahn decomposition of the pair of measures.

**Bounds.**

* `abs_measureReal_sub_le_tvDist`, `abs_measureReal_sub_le_half_tvDist`: for a measurable `A`,
  `|μ A - ν A| ≤ ‖μ - ν‖`, and `≤ ‖μ - ν‖ / 2` for probability measures.
* `abs_integral_sub_integral_le_tvDist`: for a measurable `φ` with `|φ| ≤ C`,
  `|∫ φ dμ - ∫ φ dν| ≤ C ‖μ - ν‖`.
* `tvDist_map_le`: an image under a measurable map does not increase the distance;
  `tvDist_map_eq_of_leftInverse`: a map with a measurable left inverse preserves it.
* `tvDist_withDensity_le`: for two laws with densities `f, g` against a common measure,
  `‖μ - ν‖ ≤ ∫ |f - g|`.

**The Bernstein and von Mises predicates.** A sequence of random posterior laws `Π_n(ω)` (one
probability law on the parameter space `E` for every sample size `n` and data value `ω`), a
centering `θ̂_n(ω)` and a limit law `N` on `E`:

* `IsBernsteinVonMises P Π θ̂ N`: the total variation distance between `Π_n` and the normal
  approximation `N(θ̂_n, n⁻¹ ·)`, the image of `N` under `z ↦ θ̂_n + n^{-1/2} z`, tends to `0`
  in probability under the sampling law `P`.
* `IsBernsteinVonMisesWeak P Π θ̂ N`: for every bounded continuous `φ`,
  `∫ φ(√n (θ - θ̂_n)) dΠ_n(θ) → ∫ φ dN` in probability.

These are hypotheses, not theorems: the Bernstein and von Mises theorem asserts the total
variation form for regular parametric models (van der Vaart 1998, Theorem 10.1), and this file
does not prove it in general. `IsBernsteinVonMises.isBernsteinVonMisesWeak` shows that the total
variation form implies the weak form. The predicate is proved for the conjugate normal location
model in `PosteriorLimitNormalLocation`.

## Main definitions

* `PosteriorLimit.IsBernsteinVonMises`, `PosteriorLimit.IsBernsteinVonMisesWeak`.

## Main results

* `abs_measureReal_sub_le_tvDist`, `abs_integral_sub_integral_le_tvDist`, `tvDist_map_le`,
  `tvDist_map_eq_of_leftInverse`, `tvDist_withDensity_le`,
  `IsBernsteinVonMises.isBernsteinVonMisesWeak`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

section Bounds

variable {E : Type*} [MeasurableSpace E] {μ ν : Measure E}

/-- On a Hahn set `s` of the pair `(μ, ν)` (`μ ≤ ν` on `s`, `ν ≤ μ` off `s`), the excess of `μ`
over `ν` on any measurable set is at most its excess on `sᶜ`. -/
lemma measureReal_sub_le_of_isHahnDecomposition [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set E} (h : IsHahnDecomposition μ ν s) {A : Set E} (hA : MeasurableSet A) :
    μ.real A - ν.real A ≤ μ.real sᶜ - ν.real sᶜ := by
  have hs := h.measurableSet
  have h1 : μ.real (A ∩ s) ≤ ν.real (A ∩ s) := by
    have := h.le_on A
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA] at this
    exact ENNReal.toReal_mono (measure_ne_top _ _) this
  have h2 : ν.real (sᶜ \ A) ≤ μ.real (sᶜ \ A) := by
    have := h.ge_on_compl Aᶜ
    rw [Measure.restrict_apply hA.compl, Measure.restrict_apply hA.compl] at this
    rw [Set.sdiff_eq, Set.inter_comm]
    exact ENNReal.toReal_mono (measure_ne_top _ _) this
  have eμ := measureReal_inter_add_sdiff (μ := μ) (s := A) hs
  have eν := measureReal_inter_add_sdiff (μ := ν) (s := A) hs
  have fμ := measureReal_inter_add_sdiff (μ := μ) (s := sᶜ) hA
  have fν := measureReal_inter_add_sdiff (μ := ν) (s := sᶜ) hA
  have hAs : A \ s = sᶜ ∩ A := by rw [Set.sdiff_eq, Set.inter_comm]
  rw [hAs] at eμ eν
  linarith

/-- The total variation distance as the sum of the two excesses on a Hahn set, both nonnegative.
-/
lemma tvDist_eq_of_isHahnDecomposition [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Set E}
    (h : IsHahnDecomposition μ ν s) :
    tvDist μ ν = (ν.real s - μ.real s) + (μ.real sᶜ - ν.real sᶜ) ∧
      0 ≤ ν.real s - μ.real s ∧ 0 ≤ μ.real sᶜ - ν.real sᶜ := by
  refine ⟨h.tvDist_eq, ?_, ?_⟩
  · have := measureReal_sub_le_of_isHahnDecomposition h.compl h.measurableSet
    rw [compl_compl] at this
    have h0 := measureReal_sub_le_of_isHahnDecomposition h.compl MeasurableSet.empty
    simp only [measureReal_empty, sub_zero, compl_compl] at h0
    linarith
  · have h0 := measureReal_sub_le_of_isHahnDecomposition h MeasurableSet.empty
    simp only [measureReal_empty, sub_zero] at h0
    linarith

/-- **Set probabilities under nearby laws.** For finite measures and a measurable set `A`,
`|μ A - ν A| ≤ ‖μ - ν‖`. -/
theorem abs_measureReal_sub_le_tvDist [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set E}
    (hA : MeasurableSet A) : |μ.real A - ν.real A| ≤ tvDist μ ν := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  obtain ⟨he, h0, h1⟩ := tvDist_eq_of_isHahnDecomposition h
  have a1 := measureReal_sub_le_of_isHahnDecomposition h hA
  have a2 := measureReal_sub_le_of_isHahnDecomposition h.compl hA
  rw [compl_compl] at a2
  rw [abs_le, he]
  constructor <;> linarith

/-- **Set probabilities under nearby probability laws.** For probability measures and a
measurable set `A`, `|μ A - ν A| ≤ ‖μ - ν‖ / 2`: the two excesses on a Hahn set are equal. -/
theorem abs_measureReal_sub_le_half_tvDist [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set E} (hA : MeasurableSet A) : |μ.real A - ν.real A| ≤ tvDist μ ν / 2 := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  obtain ⟨he, h0, h1⟩ := tvDist_eq_of_isHahnDecomposition h
  have a1 := measureReal_sub_le_of_isHahnDecomposition h hA
  have a2 := measureReal_sub_le_of_isHahnDecomposition h.compl hA
  rw [compl_compl] at a2
  have cμ := probReal_compl_eq_one_sub (μ := μ) h.measurableSet
  have cν := probReal_compl_eq_one_sub (μ := ν) h.measurableSet
  rw [abs_le, he]
  constructor <;> linarith

/-- **Integrals of bounded functions under nearby laws.** For finite measures and a measurable
`φ` with `|φ| ≤ C`, `|∫ φ dμ - ∫ φ dν| ≤ C ‖μ - ν‖`. Proof: on a Hahn set `s`, `ν|_s` is `μ|_s`
plus a measure of mass `ν s - μ s`, and `μ|_{sᶜ}` is `ν|_{sᶜ}` plus a measure of mass
`μ sᶜ - ν sᶜ`; the difference of the integrals is the difference of the integrals of `φ` against
these two measures. -/
theorem abs_integral_sub_integral_le_tvDist [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {φ : E → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) :
    |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤ C * tvDist μ ν := by
  obtain ⟨s, h⟩ := exists_isHahnDecomposition μ ν
  obtain ⟨he, h0, h1⟩ := tvDist_eq_of_isHahnDecomposition h
  have hs := h.measurableSet
  set a := ν.restrict s - μ.restrict s with ha_def
  set b := μ.restrict sᶜ - ν.restrict sᶜ with hb_def
  have ha : ν.restrict s = a + μ.restrict s := (Measure.sub_add_cancel_of_le h.le_on).symm
  have hb : μ.restrict sᶜ = b + ν.restrict sᶜ := (Measure.sub_add_cancel_of_le h.ge_on_compl).symm
  have : IsFiniteMeasure a := by
    refine ⟨lt_of_le_of_lt ?_ (measure_lt_top (ν.restrict s) Set.univ)⟩
    rw [ha]
    exact le_add_right le_rfl
  have : IsFiniteMeasure b := by
    refine ⟨lt_of_le_of_lt ?_ (measure_lt_top (μ.restrict sᶜ) Set.univ)⟩
    rw [hb]
    exact le_add_right le_rfl
  have hint : ∀ ρ : Measure E, IsFiniteMeasure ρ → Integrable φ ρ := fun ρ _ ↦
    Integrable.of_bound hφ.aestronglyMeasurable C (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs]; exact hC x)
  have hamass : a.real Set.univ = ν.real s - μ.real s := by
    rw [measureReal_def, ha_def, Measure.sub_apply MeasurableSet.univ h.le_on,
      ENNReal.toReal_sub_of_le (h.le_on Set.univ) (measure_ne_top _ _)]
    simp [Measure.restrict_apply MeasurableSet.univ, measureReal_def]
  have hbmass : b.real Set.univ = μ.real sᶜ - ν.real sᶜ := by
    rw [measureReal_def, hb_def, Measure.sub_apply MeasurableSet.univ h.ge_on_compl,
      ENNReal.toReal_sub_of_le (h.ge_on_compl Set.univ) (measure_ne_top _ _)]
    simp [Measure.restrict_apply MeasurableSet.univ, measureReal_def]
  have hμsplit := integral_add_compl hs (hint μ inferInstance)
  have hνsplit := integral_add_compl hs (hint ν inferInstance)
  have hνs : ∫ x in s, φ x ∂ν = ∫ x, φ x ∂a + ∫ x in s, φ x ∂μ := by
    rw [ha, integral_add_measure (hint a inferInstance) (hint _ inferInstance)]
  have hμs : ∫ x in sᶜ, φ x ∂μ = ∫ x, φ x ∂b + ∫ x in sᶜ, φ x ∂ν := by
    rw [hb, integral_add_measure (hint b inferInstance) (hint _ inferInstance)]
  have hba : ‖∫ x, φ x ∂a‖ ≤ C * a.real Set.univ :=
    norm_integral_le_of_norm_le_const (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)
  have hbb : ‖∫ x, φ x ∂b‖ ≤ C * b.real Set.univ :=
    norm_integral_le_of_norm_le_const (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)
  rw [Real.norm_eq_abs, hamass] at hba
  rw [Real.norm_eq_abs, hbmass] at hbb
  rw [← hμsplit, ← hνsplit, hνs, hμs, he]
  have : ∫ x in s, φ x ∂μ + (∫ x, φ x ∂b + ∫ x in sᶜ, φ x ∂ν) -
      (∫ x, φ x ∂a + ∫ x in s, φ x ∂μ + ∫ x in sᶜ, φ x ∂ν) =
      ∫ x, φ x ∂b - ∫ x, φ x ∂a := by ring
  rw [this]
  calc |∫ x, φ x ∂b - ∫ x, φ x ∂a| ≤ |∫ x, φ x ∂b| + |∫ x, φ x ∂a| := abs_sub _ _
    _ ≤ C * (μ.real sᶜ - ν.real sᶜ) + C * (ν.real s - μ.real s) := add_le_add hbb hba
    _ = C * (ν.real s - μ.real s + (μ.real sᶜ - ν.real sᶜ)) := by ring

/-- **Images do not increase the total variation distance.** For finite measures and a
measurable map `f`, `‖f_# μ - f_# ν‖ ≤ ‖μ - ν‖`. Proof: the two excesses of `(f_# μ, f_# ν)` on
one of its Hahn sets are excesses of `(μ, ν)` on preimages, each bounded by the matching excess
on a Hahn set of `(μ, ν)`. -/
theorem tvDist_map_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] {F : Type*} [MeasurableSpace F]
    {f : E → F} (hf : Measurable f) : tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  obtain ⟨t, ht⟩ := exists_isHahnDecomposition (μ.map f) (ν.map f)
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  have htm := ht.measurableSet
  rw [ht.tvDist_eq, (tvDist_eq_of_isHahnDecomposition hs).1,
    map_measureReal_apply hf htm, map_measureReal_apply hf htm,
    map_measureReal_apply hf htm.compl, map_measureReal_apply hf htm.compl]
  have a1 := measureReal_sub_le_of_isHahnDecomposition hs (hf htm.compl)
  have a2 := measureReal_sub_le_of_isHahnDecomposition hs.compl (hf htm)
  rw [compl_compl] at a2
  linarith

/-- **Maps with a measurable left inverse preserve the total variation distance**, for example
the affine maps `z ↦ a + c z` with `c ≠ 0` of a normed space. -/
theorem tvDist_map_eq_of_leftInverse [IsFiniteMeasure μ] [IsFiniteMeasure ν] {F : Type*}
    [MeasurableSpace F] {f : E → F} {g : F → E} (hf : Measurable f) (hg : Measurable g)
    (hgf : ∀ x, g (f x) = x) : tvDist (μ.map f) (ν.map f) = tvDist μ ν := by
  refine le_antisymm (tvDist_map_le hf) ?_
  have hid : (g ∘ f) = id := funext hgf
  have hμ : (μ.map f).map g = μ := by rw [Measure.map_map hg hf, hid, Measure.map_id]
  have hν : (ν.map f).map g = ν := by rw [Measure.map_map hg hf, hid, Measure.map_id]
  calc tvDist μ ν = tvDist ((μ.map f).map g) ((ν.map f).map g) := by rw [hμ, hν]
    _ ≤ tvDist (μ.map f) (ν.map f) := tvDist_map_le hg

/-- The mass of a set under a law with a nonnegative integrable real density. -/
lemma measureReal_withDensity_ofReal {ρ : Measure E} {f : E → ℝ} (hf : Integrable f ρ)
    (hf0 : ∀ x, 0 ≤ f x) {A : Set E} (hA : MeasurableSet A) :
    (ρ.withDensity fun x ↦ ENNReal.ofReal (f x)).real A = ∫ x in A, f x ∂ρ := by
  rw [measureReal_def, withDensity_apply _ hA,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ hf0 x) hf.aestronglyMeasurable.restrict]

/-- **Total variation between laws with densities.** For nonnegative integrable densities `f, g`
against a common measure `ρ`, `‖f ρ - g ρ‖ ≤ ∫ |f - g| dρ`. -/
theorem tvDist_withDensity_le {ρ : Measure E} {f g : E → ℝ} (hf : Integrable f ρ)
    (hg : Integrable g ρ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    tvDist (ρ.withDensity fun x ↦ ENNReal.ofReal (f x))
        (ρ.withDensity fun x ↦ ENNReal.ofReal (g x)) ≤ ∫ x, |f x - g x| ∂ρ := by
  have hfin : ∀ h : E → ℝ, Integrable h ρ →
      IsFiniteMeasure (ρ.withDensity fun x ↦ ENNReal.ofReal (h x)) := fun h hh ↦
    isFiniteMeasure_withDensity_ofReal hh.2
  have := hfin f hf
  have := hfin g hg
  obtain ⟨s, h⟩ := exists_isHahnDecomposition (ρ.withDensity fun x ↦ ENNReal.ofReal (f x))
    (ρ.withDensity fun x ↦ ENNReal.ofReal (g x))
  have hs := h.measurableSet
  rw [h.tvDist_eq, measureReal_withDensity_ofReal hf hf0 hs,
    measureReal_withDensity_ofReal hg hg0 hs, measureReal_withDensity_ofReal hf hf0 hs.compl,
    measureReal_withDensity_ofReal hg hg0 hs.compl,
    ← integral_sub hg.integrableOn hf.integrableOn, ← integral_sub hf.integrableOn hg.integrableOn,
    ← integral_add_compl hs (f := fun x ↦ |f x - g x|) (hf.sub hg).abs]
  refine add_le_add (setIntegral_mono (hg.sub hf).integrableOn (hf.sub hg).abs.integrableOn
    fun x ↦ ?_) (setIntegral_mono (hf.sub hg).integrableOn (hf.sub hg).abs.integrableOn
    fun x ↦ le_abs_self _)
  rw [abs_sub_comm]
  exact le_abs_self _

end Bounds

/-! ### The Bernstein and von Mises predicates -/

section Predicates

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [MeasurableSpace E]

/-- **The Bernstein and von Mises conclusion, total variation form.** The random posterior laws
`Pn n ω` on the parameter space are probability laws, the limit `N` is a probability law, and
`‖Π_n - N(θ̂_n, n⁻¹ ·)‖ → 0` in probability under the sampling law `P`, where `N(θ̂_n, n⁻¹ ·)` is
the image of `N` under `z ↦ θ̂_n + n^{-1/2} z`. For a regular parametric model with an efficient
estimator `θ̂_n` and a prior with a density continuous and positive at the truth, `N` is
`N(0, I⁻¹)` with `I` the Fisher information (van der Vaart 1998, Theorem 10.1). This is a
hypothesis; it is not proved here in general. -/
structure IsBernsteinVonMises (P : Measure Ω) (Pn : ℕ → Ω → Measure E) (θh : ℕ → Ω → E)
    (N : Measure E) : Prop where
  /-- Every posterior is a probability law. -/
  isProbabilityMeasure : ∀ n ω, IsProbabilityMeasure (Pn n ω)
  /-- The limit law is a probability law. -/
  isProbabilityMeasure_limit : IsProbabilityMeasure N
  /-- The total variation distance to the normal approximation tends to zero in probability. -/
  tendsto : TendstoInMeasure P
    (fun n ω ↦ tvDist (Pn n ω) (N.map fun z ↦ θh n ω + (√(n : ℝ))⁻¹ • z)) atTop (fun _ ↦ 0)

/-- **The Bernstein and von Mises conclusion, weak form.** The posteriors and the limit are
probability laws, and for every bounded continuous `φ` the posterior mean of
`φ(√n (θ - θ̂_n))` converges in probability to `∫ φ dN`: the posterior law of the rescaled
parameter converges weakly to `N`, in probability. This is a hypothesis; the total variation form
implies it (`IsBernsteinVonMises.isBernsteinVonMisesWeak`). -/
structure IsBernsteinVonMisesWeak (P : Measure Ω) (Pn : ℕ → Ω → Measure E) (θh : ℕ → Ω → E)
    (N : Measure E) : Prop where
  /-- Every posterior is a probability law. -/
  isProbabilityMeasure : ∀ n ω, IsProbabilityMeasure (Pn n ω)
  /-- The limit law is a probability law. -/
  isProbabilityMeasure_limit : IsProbabilityMeasure N
  /-- Posterior means of bounded continuous functions of the rescaled parameter converge. -/
  tendsto : ∀ φ : E → ℝ, Continuous φ → (∃ C, ∀ z, |φ z| ≤ C) →
    TendstoInMeasure P (fun n ω ↦ ∫ θ, φ (√(n : ℝ) • (θ - θh n ω)) ∂Pn n ω) atTop
      (fun _ ↦ ∫ z, φ z ∂N)

variable [BorelSpace E]

/-- **The total variation form implies the weak form.** Under the normal approximation
`N(θ̂_n, n⁻¹ ·)` the rescaled parameter `√n (θ - θ̂_n)` has law exactly `N` for `n ≥ 1`, and
`|∫ ψ dΠ_n - ∫ ψ dN(θ̂_n, n⁻¹ ·)| ≤ C ‖Π_n - N(θ̂_n, n⁻¹ ·)‖` for `|ψ| ≤ C`
(`abs_integral_sub_integral_le_tvDist`). -/
theorem IsBernsteinVonMises.isBernsteinVonMisesWeak {P : Measure Ω} {Pn : ℕ → Ω → Measure E}
    {θh : ℕ → Ω → E} {N : Measure E} (h : IsBernsteinVonMises P Pn θh N) :
    IsBernsteinVonMisesWeak P Pn θh N := by
  have := h.isProbabilityMeasure
  have := h.isProbabilityMeasure_limit
  refine ⟨h.isProbabilityMeasure, h.isProbabilityMeasure_limit, fun φ hφ ⟨C, hC⟩ ↦ ?_⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have key : ∀ n : ℕ, 1 ≤ n → ∀ ω, |∫ θ, φ (√(n : ℝ) • (θ - θh n ω)) ∂Pn n ω - ∫ z, φ z ∂N| ≤
      C * tvDist (Pn n ω) (N.map fun z ↦ θh n ω + (√(n : ℝ))⁻¹ • z) := by
    intro n hn ω
    have hsq : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
    set a : E → E := fun z ↦ θh n ω + (√(n : ℝ))⁻¹ • z with ha
    have ham : Measurable a := by fun_prop
    have hψ : Continuous fun θ : E ↦ φ (√(n : ℝ) • (θ - θh n ω)) := by fun_prop
    have hNa : ∫ θ, φ (√(n : ℝ) • (θ - θh n ω)) ∂N.map a = ∫ z, φ z ∂N := by
      rw [integral_map ham.aemeasurable hψ.aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
      simp only [ha, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hsq, one_smul]
    have : IsProbabilityMeasure (N.map a) :=
      (Measure.isProbabilityMeasure_map_iff ham.aemeasurable).2 inferInstance
    have hb := abs_integral_sub_integral_le_tvDist (μ := Pn n ω) (ν := N.map a) hψ.measurable
      (fun θ ↦ hC _)
    rwa [hNa] at hb
  rw [tendstoInMeasure_iff_dist]
  have htv := h.tendsto
  rw [tendstoInMeasure_iff_dist] at htv
  intro ε hε
  have hη : 0 < ε / (C + 1) := by positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (htv _ hη)
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  have hk := key n hn ω
  have ht0 := tvDist_nonneg (μ := Pn n ω) (ν := N.map fun z ↦ θh n ω + (√(n : ℝ))⁻¹ • z)
  rw [abs_of_nonneg ht0, div_le_iff₀ (by linarith)]
  nlinarith

end Predicates

end PosteriorLimit

end CausalInference
