/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ConjugacyKernel

/-!
# Bayes' theorem for a likelihood with a density

A dominated statistical model is given by a jointly measurable density `p(ξ, y)` of the data
`y ∈ Y` with respect to an s-finite measure `ν`, for each parameter `ξ ∈ Ξ`. It defines the
**likelihood kernel** `ξ ↦ p(ξ, ·) ν` (`likelihoodKernel`). With a finite prior `μ` the joint law
of parameter and data is `μ ⊗ κ`, the marginal law of the data is `κ ∘ μ`, and Mathlib's
posterior kernel `κ†μ` (`ProbabilityTheory.posterior`) is the conditional law of the parameter
given the data, determined almost everywhere under `κ ∘ μ`.

The library writes a posterior in the normalized form of `MetaAnalysis.Conjugacy`: the prior
reweighted by the likelihood and divided by the marginal likelihood `Z(y) = ∫ p(ξ, y) dμ(ξ)`,
`Z(y)⁻¹ • μ.withDensity (p(·, y))` (`normalizedPosterior`).

## Main definitions

* `likelihoodKernel`, `normalizedPosterior`.

## Main results

* `comp_likelihoodKernel`: the marginal law of the data has density `Z` with respect to `ν`.
* `posterior_likelihoodKernel` (**Bayes' theorem**): for almost every `y` under the marginal law,
  `0 < Z(y) < ∞` and `(κ†μ)(y) = Z(y)⁻¹ • μ.withDensity (p(·, y))`. The two conditions on `Z` are
  conclusions, not hypotheses.
* `normalizedPosterior_withDensity`: with a prior density `π`, the posterior density
  `p(ξ, y) π(ξ) / ∫ p π`.
* `normalizedPosterior_const_mul`, `posterior_likelihoodKernel_factor` (**sufficiency form**): if
  `p(ξ, y) = h(y) g(ξ, T y)`, the posterior depends on the data only through `T y`, almost
  everywhere under the marginal law; no positivity of `h` is assumed, it holds almost everywhere.
* `normalizedPosterior_singleton_div`: **posterior odds** are prior odds times the likelihood
  ratio; `normalizedPosterior_bool_odds`: the Bayes factor form for two models.
* `normalizedPosterior_eq_of_mul_eq`: if prior density times likelihood is a constant multiple
  of a probability density, the posterior has that density (the conjugate update).
* `commonEffectKernel_eq_likelihoodKernel`: the kernel of `MetaAnalysis.ConjugacyKernel` is a
  likelihood kernel.

## References

* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ξ Y : Type*} [MeasurableSpace Ξ] [MeasurableSpace Y]

/-- The **normalized posterior** `Z⁻¹ • μ.withDensity L`, `Z = ∫ L dμ`: the prior reweighted by
the likelihood `L` and divided by the marginal likelihood. It is a probability measure exactly
when `0 < Z < ∞` (`isProbabilityMeasure_normalizedPosterior`). -/
noncomputable def normalizedPosterior (μ : Measure Ξ) (L : Ξ → ℝ≥0∞) : Measure Ξ :=
  (∫⁻ ξ, L ξ ∂μ)⁻¹ • μ.withDensity L

theorem normalizedPosterior_apply (μ : Measure Ξ) (L : Ξ → ℝ≥0∞) {A : Set Ξ}
    (hA : MeasurableSet A) :
    normalizedPosterior μ L A = (∫⁻ ξ, L ξ ∂μ)⁻¹ * ∫⁻ ξ in A, L ξ ∂μ := by
  rw [normalizedPosterior, smul_apply, withDensity_apply _ hA, smul_eq_mul]

/-- The normalized posterior is a probability measure when the marginal likelihood is positive
and finite. -/
theorem isProbabilityMeasure_normalizedPosterior {μ : Measure Ξ} {L : Ξ → ℝ≥0∞}
    (h0 : ∫⁻ ξ, L ξ ∂μ ≠ 0) (htop : ∫⁻ ξ, L ξ ∂μ ≠ ∞) :
    IsProbabilityMeasure (normalizedPosterior μ L) :=
  ⟨by rw [normalizedPosterior_apply _ _ MeasurableSet.univ, Measure.restrict_univ,
    ENNReal.inv_mul_cancel h0 htop]⟩

/-- **Bayes' formula with a prior density**: if the prior is `π κ`, the posterior is
`(∫ L π dκ)⁻¹ • κ.withDensity (L π)`, that is, it has the density `L(ξ) π(ξ) / ∫ L π dκ` with
respect to `κ`. -/
theorem normalizedPosterior_withDensity {κ : Measure Ξ} {π L : Ξ → ℝ≥0∞} (hπ : Measurable π)
    (hL : Measurable L) :
    normalizedPosterior (κ.withDensity π) L =
      normalizedPosterior κ fun ξ => L ξ * π ξ := by
  rw [normalizedPosterior, normalizedPosterior, lintegral_withDensity_eq_lintegral_mul _ hπ hL,
    ← withDensity_mul κ hπ hL]
  have e : π * L = fun ξ => L ξ * π ξ := by
    funext ξ
    simp only [Pi.mul_apply, mul_comm (π _)]
  simp only [e]

/-- **Conjugate updating**: if the prior has density `f` with respect to `κ` and `f L = c g`
almost everywhere, with `0 < c < ∞` and `g` a probability density, then the marginal likelihood
is `c` and the posterior is `κ.withDensity g`. -/
theorem normalizedPosterior_eq_of_mul_eq {κ : Measure Ξ} {f L g : Ξ → ℝ≥0∞}
    (hf : Measurable f) (hL : Measurable L) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (hfg : ∀ᵐ ξ ∂κ, f ξ * L ξ = c * g ξ) (hg1 : ∫⁻ ξ, g ξ ∂κ = 1) :
    ∫⁻ ξ, L ξ ∂κ.withDensity f = c ∧
      normalizedPosterior (κ.withDensity f) L = κ.withDensity g := by
  have hZ : ∫⁻ ξ, L ξ ∂κ.withDensity f = c := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hf hL,
      lintegral_congr_ae (g := fun ξ => c * g ξ) (by filter_upwards [hfg] with ξ h using h),
      lintegral_const_mul' _ _ hc, hg1, mul_one]
  refine ⟨hZ, ?_⟩
  rw [normalizedPosterior, hZ, ← withDensity_mul κ hf hL]
  rw [withDensity_congr_ae (g := fun ξ => c * g ξ) (by
    filter_upwards [hfg] with ξ h using h)]
  rw [show (fun ξ => c * g ξ) = c • g from rfl, withDensity_smul' _ _ hc, smul_smul,
    ENNReal.inv_mul_cancel hc0 hc, one_smul]

/-- **Invariance under a constant factor**: multiplying the likelihood by `0 < c < ∞` leaves the
normalized posterior unchanged. -/
theorem normalizedPosterior_const_mul (μ : Measure Ξ) (L : Ξ → ℝ≥0∞) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    (hc : c ≠ ∞) :
    normalizedPosterior μ (fun ξ => c * L ξ) = normalizedPosterior μ L := by
  rw [normalizedPosterior, normalizedPosterior, lintegral_const_mul' _ _ hc,
    show (fun ξ => c * L ξ) = c • L from rfl, withDensity_smul' _ _ hc, smul_smul,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hc), mul_comm c⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel hc0 hc, mul_one]

/-- The **likelihood kernel** `ξ ↦ p(ξ, ·) ν` of a dominated model with density `p(ξ, y)` of the
data with respect to `ν`. -/
noncomputable def likelihoodKernel (ν : Measure Y) [SFinite ν] (p : Ξ → Y → ℝ≥0∞) :
    Kernel Ξ Y :=
  Kernel.withDensity (Kernel.const Ξ ν) p

theorem likelihoodKernel_apply {ν : Measure Y} [SFinite ν] {p : Ξ → Y → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) (ξ : Ξ) :
    likelihoodKernel ν p ξ = ν.withDensity (p ξ) := by
  rw [likelihoodKernel, Kernel.withDensity_apply _ hp, Kernel.const_apply]

/-- The likelihood kernel is a Markov kernel when every `p(ξ, ·)` is a probability density. -/
theorem isMarkovKernel_likelihoodKernel {ν : Measure Y} [SFinite ν] {p : Ξ → Y → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) (hp1 : ∀ ξ, ∫⁻ y, p ξ y ∂ν = 1) :
    IsMarkovKernel (likelihoodKernel ν p) :=
  ⟨fun ξ => ⟨by rw [likelihoodKernel_apply hp, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, hp1]⟩⟩

/-- **The marginal law of the data** has the density `Z(y) = ∫ p(ξ, y) dμ(ξ)` with respect to
`ν`. Proof: Tonelli. -/
theorem comp_likelihoodKernel {ν : Measure Y} [SFinite ν] {p : Ξ → Y → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) (μ : Measure Ξ) [SFinite μ] :
    likelihoodKernel ν p ∘ₘ μ = ν.withDensity fun y => ∫⁻ ξ, p ξ y ∂μ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), withDensity_apply _ hs]
  simp_rw [likelihoodKernel_apply hp, withDensity_apply _ hs]
  exact lintegral_lintegral_swap hp.aemeasurable

/-- The kernel `θ ↦ ⊗ᵢ N(θ, sᵢ)` of `MetaAnalysis.ConjugacyKernel` is the likelihood kernel of
the common effect likelihood with respect to Lebesgue measure. -/
theorem commonEffectKernel_eq_likelihoodKernel {ι : Type*} [Fintype ι] (s : ι → ℝ) :
    commonEffectKernel s = likelihoodKernel (Measure.pi fun _ : ι => (volume : Measure ℝ))
      (fun θ y => ENNReal.ofReal (commonEffectLikelihood s θ y)) :=
  rfl

/-- **Bayes' theorem.** Let the parameter space be standard Borel, the prior `μ` finite, and the
data have the jointly measurable density `p(ξ, y)` with respect to an s-finite `ν`, with a finite
likelihood kernel `κ = likelihoodKernel ν p` (for example every `p(ξ, ·)` a probability density,
`isMarkovKernel_likelihoodKernel`). Then for almost every `y` under the marginal law `κ ∘ μ`,
the marginal likelihood `Z(y) = ∫ p(ξ, y) dμ(ξ)` lies in `(0, ∞)` and the posterior kernel is
`(κ†μ)(y) = Z(y)⁻¹ • μ.withDensity (p(·, y))`. Proof: the kernel equal to the normalized
posterior where `0 < Z < ∞` (and to `μ(Ξ)⁻¹ μ` elsewhere) disintegrates the joint law, by
Tonelli on rectangles; uniqueness of the disintegration. -/
theorem posterior_likelihoodKernel [StandardBorelSpace Ξ] [Nonempty Ξ] {ν : Measure Y}
    [SFinite ν] {μ : Measure Ξ} [IsFiniteMeasure μ] {p : Ξ → Y → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) [IsFiniteKernel (likelihoodKernel ν p)] :
    ∀ᵐ y ∂(likelihoodKernel ν p ∘ₘ μ), 0 < ∫⁻ ξ, p ξ y ∂μ ∧ ∫⁻ ξ, p ξ y ∂μ < ∞ ∧
      ((likelihoodKernel ν p)†μ) y = normalizedPosterior μ (fun ξ => p ξ y) := by
  classical
  set κ := likelihoodKernel ν p
  set m : Y → ℝ≥0∞ := fun y => ∫⁻ ξ, p ξ y ∂μ with hm_def
  have hm : Measurable m := hp.lintegral_prod_left'
  have hcomp : κ ∘ₘ μ = ν.withDensity m := comp_likelihoodKernel hp μ
  have htot : ∫⁻ y, m y ∂ν ≠ ∞ := by
    have h1 : (κ ∘ₘ μ) Set.univ ≠ ∞ := measure_ne_top _ _
    rwa [hcomp, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  have hfin : ∀ᵐ y ∂ν, m y < ∞ := ae_lt_top hm htot
  set G : Set Y := {y | m y ≠ 0 ∧ m y ≠ ∞} with hG
  have hGm : MeasurableSet G :=
    ((measurableSet_singleton 0).preimage hm).compl.inter
      ((measurableSet_singleton ∞).preimage hm).compl
  have hgood : ∀ᵐ y ∂(κ ∘ₘ μ), y ∈ G := by
    rw [hcomp, ae_withDensity_iff hm]
    filter_upwards [hfin] with y hy h0 using ⟨h0, hy.ne⟩
  by_cases hμ0 : μ = 0
  · have : κ ∘ₘ μ = 0 := by rw [hμ0, Measure.bind_zero_left]
    rw [this, ae_zero]
    exact Filter.eventually_bot
  have hμu : μ Set.univ ≠ 0 := by rwa [Ne, Measure.measure_univ_eq_zero]
  set f : Y → Ξ → ℝ≥0∞ := fun y ξ => if y ∈ G then (m y)⁻¹ * p ξ y else (μ Set.univ)⁻¹
    with hf_def
  have hf : Measurable (Function.uncurry f) :=
    Measurable.ite (hGm.preimage measurable_fst)
      ((hm.comp measurable_fst).inv.mul (hp.comp measurable_swap)) measurable_const
  set η : Kernel Y Ξ := Kernel.withDensity (Kernel.const Y μ) f with hη_def
  have hη : ∀ y, η y = μ.withDensity (f y) := fun y => by
    rw [hη_def, Kernel.withDensity_apply _ hf, Kernel.const_apply]
  have hηm : IsMarkovKernel η := ⟨fun y => ⟨by
    rw [hη, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    by_cases hy : y ∈ G
    · simp only [hf_def, hy, ↓reduceIte]
      rw [lintegral_const_mul _ hp.of_uncurry_right,
        ENNReal.inv_mul_cancel hy.1 hy.2]
    · simp only [hf_def, hy, ↓reduceIte, lintegral_const]
      exact ENNReal.inv_mul_cancel hμu (measure_ne_top _ _)⟩⟩
  have hjoint : (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap := by
    refine Measure.ext_prod fun {s t} hs ht => ?_
    rw [Measure.compProd_apply_prod hs ht, Measure.map_apply measurable_swap (hs.prod ht),
      Set.preimage_swap_prod, Measure.compProd_apply_prod ht hs, hcomp,
      setLIntegral_withDensity_eq_setLIntegral_mul _ hm (η.measurable_coe ht) hs]
    have hlhs : ∫⁻ y in s, (m * fun y => η y t) y ∂ν = ∫⁻ y in s, ∫⁻ ξ in t, p ξ y ∂μ ∂ν := by
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hfin] with y hy
      simp only [Pi.mul_apply, hη, withDensity_apply _ ht]
      by_cases hyG : y ∈ G
      · simp only [hf_def, hyG, ↓reduceIte]
        rw [lintegral_const_mul _ hp.of_uncurry_right, ← mul_assoc,
          ENNReal.mul_inv_cancel hyG.1 hyG.2, one_mul]
      · have h0 : m y = 0 := by
          by_contra h0
          exact hyG ⟨h0, hy.ne⟩
        have : ∫⁻ ξ in t, p ξ y ∂μ = 0 :=
          le_antisymm ((setLIntegral_le_lintegral t _).trans h0.le) zero_le
        rw [h0, this, zero_mul]
    rw [hlhs]
    simp_rw [κ, likelihoodKernel_apply hp, withDensity_apply _ hs]
    exact lintegral_lintegral_swap (hp.comp measurable_swap).aemeasurable
  have hae := ae_eq_posterior_of_compProd_eq hjoint
  filter_upwards [hgood, hae] with y hyG he
  refine ⟨pos_iff_ne_zero.2 hyG.1, lt_top_iff_ne_top.2 hyG.2, ?_⟩
  rw [← he, hη, normalizedPosterior]
  simp only [hf_def, hyG, ↓reduceIte]
  rw [show (fun ξ => (m y)⁻¹ * p ξ y) = (m y)⁻¹ • fun ξ => p ξ y from rfl,
    withDensity_smul' _ _ (ENNReal.inv_ne_top.2 hyG.1)]

/-- **The posterior depends on the data only through a sufficient statistic.** If the density
factors as `p(ξ, y) = h(y) g(ξ, T y)` with `h` and `g` arbitrary (jointly measurable), then for
almost every `y` under the marginal law `κ ∘ μ` the posterior is the normalized posterior of the
likelihood `g(·, T y)`, and `0 < h(y) < ∞`. Proof: almost surely `0 < Z(y) = h(y) ∫ g(·, T y) dμ
< ∞` (`posterior_likelihoodKernel`), which forces `0 < h(y) < ∞`; then
`normalizedPosterior_const_mul`. -/
theorem posterior_likelihoodKernel_factor [StandardBorelSpace Ξ] [Nonempty Ξ] {ν : Measure Y}
    [SFinite ν] {μ : Measure Ξ} [IsFiniteMeasure μ] {p : Ξ → Y → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) [IsFiniteKernel (likelihoodKernel ν p)]
    {S : Type*} (h : Y → ℝ≥0∞) (g : Ξ → S → ℝ≥0∞) (T : Y → S)
    (hg : ∀ y, Measurable fun ξ => g ξ (T y)) (hfac : ∀ ξ y, p ξ y = h y * g ξ (T y)) :
    ∀ᵐ y ∂(likelihoodKernel ν p ∘ₘ μ), 0 < h y ∧ h y < ∞ ∧
      ((likelihoodKernel ν p)†μ) y = normalizedPosterior μ (fun ξ => g ξ (T y)) := by
  filter_upwards [posterior_likelihoodKernel (μ := μ) hp] with y ⟨h0, htop, hpost⟩
  have hZ : ∫⁻ ξ, p ξ y ∂μ = h y * ∫⁻ ξ, g ξ (T y) ∂μ := by
    simp_rw [hfac]
    exact lintegral_const_mul _ (hg y)
  rw [hZ] at h0 htop
  have hh0 : h y ≠ 0 := fun h' => by simp [h'] at h0
  have hg0 : ∫⁻ ξ, g ξ (T y) ∂μ ≠ 0 := fun h' => by simp [h'] at h0
  have hhtop : h y ≠ ∞ := fun h' => by
    rw [h', ENNReal.top_mul hg0] at htop
    exact lt_irrefl _ htop
  refine ⟨pos_iff_ne_zero.2 hh0, lt_top_iff_ne_top.2 hhtop, ?_⟩
  rw [hpost]
  simp_rw [hfac]
  exact normalizedPosterior_const_mul μ _ hh0 hhtop

/-- **Posterior odds of two sets**: the ratio of the posterior probabilities of `A` and `B` is the
ratio of the prior integrals of the likelihood over them, whenever the marginal likelihood is
positive and finite. -/
theorem normalizedPosterior_div {μ : Measure Ξ} {L : Ξ → ℝ≥0∞} (h0 : ∫⁻ ξ, L ξ ∂μ ≠ 0)
    (htop : ∫⁻ ξ, L ξ ∂μ ≠ ∞) {A B : Set Ξ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    normalizedPosterior μ L A / normalizedPosterior μ L B =
      (∫⁻ ξ in A, L ξ ∂μ) / ∫⁻ ξ in B, L ξ ∂μ := by
  rw [normalizedPosterior_apply _ _ hA, normalizedPosterior_apply _ _ hB, div_eq_mul_inv,
    div_eq_mul_inv, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 htop))
      (Or.inl (ENNReal.inv_ne_top.2 h0)), inv_inv]
  rw [show (∫⁻ ξ, L ξ ∂μ)⁻¹ * (∫⁻ ξ in A, L ξ ∂μ) * ((∫⁻ ξ, L ξ ∂μ) * (∫⁻ ξ in B, L ξ ∂μ)⁻¹) =
      ((∫⁻ ξ, L ξ ∂μ)⁻¹ * (∫⁻ ξ, L ξ ∂μ)) * ((∫⁻ ξ in A, L ξ ∂μ) * (∫⁻ ξ in B, L ξ ∂μ)⁻¹) by
    ring, ENNReal.inv_mul_cancel h0 htop, one_mul]

/-- **Posterior odds equal prior odds times the likelihood ratio.** For two parameter values `a`,
`b` with `μ{b} > 0`, `0 < L(b) < ∞` and a finite marginal likelihood (positivity of the marginal
likelihood follows from `μ{b} L(b) > 0`; `L(a) μ{a}` is finite because it is at most the marginal
likelihood, and both sides vanish when `L(a) = ∞` and `μ{a} = 0`):
`P(a | y) / P(b | y) = (L(a) / L(b)) · (μ{a} / μ{b})`, in real numbers. Finiteness of the
marginal likelihood is a hypothesis: on an infinite parameter space it does not follow from the
others (on a finite one, see `normalizedPosterior_bool_odds`). -/
theorem normalizedPosterior_singleton_div [MeasurableSingletonClass Ξ] {μ : Measure Ξ}
    [IsFiniteMeasure μ] {L : Ξ → ℝ≥0∞} (htop : ∫⁻ ξ, L ξ ∂μ ≠ ∞) {a b : Ξ}
    (hb : μ {b} ≠ 0) (hLb0 : L b ≠ 0) (hLb : L b ≠ ∞) :
    (normalizedPosterior μ L {a}).toReal / (normalizedPosterior μ L {b}).toReal =
      (L a).toReal / (L b).toReal * ((μ {a}).toReal / (μ {b}).toReal) := by
  have hsing : ∀ c, normalizedPosterior μ L {c} = (∫⁻ ξ, L ξ ∂μ)⁻¹ * (L c * μ {c}) := fun c => by
    rw [normalizedPosterior_apply _ _ (measurableSet_singleton c), lintegral_singleton]
  have h0 : ∫⁻ ξ, L ξ ∂μ ≠ 0 := by
    intro h
    have hle : ∫⁻ ξ in {b}, L ξ ∂μ ≤ ∫⁻ ξ, L ξ ∂μ := setLIntegral_le_lintegral _ _
    rw [lintegral_singleton, h] at hle
    exact mul_ne_zero hLb0 hb (le_antisymm hle zero_le)
  have hZr : 0 < (∫⁻ ξ, L ξ ∂μ)⁻¹.toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0)
  have hbr : 0 < (μ {b}).toReal := ENNReal.toReal_pos hb (measure_ne_top _ _)
  have hLbr : 0 < (L b).toReal := ENNReal.toReal_pos hLb0 hLb
  simp only [hsing, ENNReal.toReal_mul]
  field_simp

/-- **Posterior odds of two models and the Bayes factor**: with the model index in `Bool`, prior
probabilities `π(M₀) > 0` and evidences `p(y | M₀) ∈ (0, ∞)`, `p(y | M₁) < ∞`, the posterior
odds of `M₁` against `M₀` are the Bayes factor `p(y | M₁) / p(y | M₀)` times the prior odds. The
marginal likelihood is finite here because the parameter space is finite. -/
theorem normalizedPosterior_bool_odds {μ : Measure Bool} [IsFiniteMeasure μ] {ev : Bool → ℝ≥0∞}
    (hp0 : μ {false} ≠ 0) (he0 : ev false ≠ 0) (he0' : ev false ≠ ∞) (he1' : ev true ≠ ∞) :
    (normalizedPosterior μ ev {true}).toReal / (normalizedPosterior μ ev {false}).toReal =
      (ev true).toReal / (ev false).toReal * ((μ {true}).toReal / (μ {false}).toReal) := by
  refine normalizedPosterior_singleton_div ?_ hp0 he0 he0'
  rw [lintegral_fintype]
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top he1' (measure_ne_top _ _),
    ENNReal.mul_ne_top he0' (measure_ne_top _ _)⟩

end MetaAnalysis

end CausalInference
