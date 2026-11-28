/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.ReductionLikelihood
public import CausalInference.NetworkMetaAnalysis.Deviance
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Count

/-!
# The aggregate marginal likelihood

A patient of an arm with aggregate data has covariates `X` drawn from the covariate law `F` of the
study and, given `X = x`, an outcome with density `L(x, ·)` with respect to a dominating measure
`ν`. The covariates are not reported, so the outcome enters the likelihood through its marginal
law.

* **The marginal density** (`snd_compProd_eq_withDensity`): the outcome of a patient drawn from
  `F` has the density `y ↦ ∫ L(x, y) F(dx)` with respect to `ν`: the individual level density
  integrated over the covariate law.
* **An arm of `n` patients** (`map_pi_compProd_eq_withDensity`): if the pairs (covariates,
  outcome) of the patients are independent with law `F ⊗ κ`, the outcome vector has the density
  `y ↦ ∏ᵢ ∫ L(x, yᵢ) F(dx)` with respect to `ν ⊗ ⋯ ⊗ ν`; a summary statistic `T` of the
  outcomes has `P(T ∈ A) = ∫_{T ∈ A} ∏ᵢ ∫ L(x, yᵢ) F(dx) dy`
  (`map_pi_compProd_summary_apply`). For a finite outcome space and the counting measure the
  summary takes the value `s` with probability `∑_{T(y) = s} ∏ᵢ ∫ L(x, yᵢ) F(dx)`
  (`map_pi_compProd_summary_singleton`).
* **The number of events of a binary outcome** (`map_pi_compProd_card_singleton`): if the event
  probability given `x` is `q(x)`, the number of events among `n` patients takes the value `s`
  with probability `(n choose s) θ^s (1 - θ)^(n - s)` with `θ = ∫ q dF`: the summary density is
  the binomial density at the aggregate event probability, which is the summary density `L(θ, s)`
  of the aggregate factor of `MultilevelModel.likelihood`. Its logarithm is
  `log (n choose s) + binomialLogLik n s θ` (`log_binomialMass`).

The finite product of measures with densities is the product measure with the product density
(`pi_withDensity`), by Tonelli's theorem for products of functions of one coordinate
(`lintegral_pi_prod`).

## Main definitions

* `binomialMass n θ s = (n choose s) θ^s (1 - θ)^(n - s)`.

## Main results

* `lintegral_pi_prod`, `pi_withDensity`, `snd_compProd_eq_withDensity`,
  `map_pi_compProd_eq_pi`, `map_pi_compProd_eq_withDensity`, `map_pi_compProd_summary_apply`,
  `map_pi_compProd_summary_singleton`, `card_filter_card_filter_eq`,
  `mem_Icc_of_count_withDensity`, `map_pi_compProd_card_singleton`, `log_binomialMass`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Products of measures with densities -/

/-- **Tonelli's theorem for a product of functions of one coordinate**: the integral of
`∏ᵢ hᵢ(yᵢ)` against a finite product of σ-finite measures is `∏ᵢ ∫ hᵢ dμᵢ`. -/
theorem lintegral_pi_prod {E : Type*} [MeasurableSpace E] :
    ∀ {n : ℕ} (μ : Fin n → Measure E) [∀ i, SigmaFinite (μ i)] (h : Fin n → E → ℝ≥0∞),
      (∀ i, Measurable (h i)) → ∫⁻ y, ∏ i, h i (y i) ∂Measure.pi μ = ∏ i, ∫⁻ x, h i x ∂μ i
  | 0, μ, _, h, _ => by simp
  | n + 1, μ, _, h, hh => by
    have hp := (measurePreserving_piFinSuccAbove (fun i => μ i) 0).symm
    rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have e : ∀ z : E × (Fin n → E), ∏ i, h i ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => E) 0).symm z i) = h 0 z.1 * ∏ i : Fin n, h i.succ (z.2 i) := by
      intro z
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp_rw [e, Fin.succAbove_zero]
    rw [lintegral_prod_mul (f := h 0) (g := fun y : Fin n → E => ∏ i, h i.succ (y i))
      (hh 0).aemeasurable
      (Finset.measurable_prod _ fun i _ => (hh i.succ).comp (measurable_pi_apply i)).aemeasurable,
      lintegral_pi_prod (fun i : Fin n => μ i.succ) (fun i => h i.succ) fun i => hh i.succ,
      Fin.prod_univ_succ]

/-- **A finite product of measures with densities** is the product of the dominating measures
with the product density: `∏ᵢ (ν with density hᵢ) = (ν ⊗ ⋯ ⊗ ν) with density y ↦ ∏ᵢ hᵢ(yᵢ)`. -/
theorem pi_withDensity {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
    (h : Fin n → E → ℝ≥0∞) (hh : ∀ i, Measurable (h i))
    [∀ i, SigmaFinite (ν.withDensity (h i))] :
    Measure.pi (fun i => ν.withDensity (h i)) =
      (Measure.pi fun _ : Fin n => ν).withDensity (fun y => ∏ i, h i (y i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have e : (Set.univ.pi s).indicator (fun y => ∏ i, h i (y i)) =
      fun y => ∏ i, (s i).indicator (h i) (y i) := by
    funext y
    by_cases hy : y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hy]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hy i trivial) _).symm
    · rw [Set.indicator_of_notMem hy]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [e, lintegral_pi_prod _ _ fun i => (hh i).indicator (hs i)]
  exact Finset.prod_congr rfl fun i _ => by
    rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

/-! ### The marginal density of an aggregate patient -/

variable {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]

/-- **The marginal density of the outcome of a patient with unreported covariates.** If the
covariates have law `F` and, for `F`-almost every `x`, the outcome law `κ x` has density
`L(x, ·)` with respect to `ν` (`L` jointly measurable), the outcome of a patient drawn from `F`,
the second marginal of `F ⊗ κ`, has density `y ↦ ∫ L(x, y) F(dx)` with respect to `ν`. -/
theorem snd_compProd_eq_withDensity (F : Measure 𝒳) [SFinite F] (ν : Measure 𝒴) [SFinite ν]
    (κ : Kernel 𝒳 𝒴) [IsSFiniteKernel κ] (L : 𝒳 → 𝒴 → ℝ≥0∞)
    (hL : Measurable (Function.uncurry L)) (hκ : ∀ᵐ x ∂F, κ x = ν.withDensity (L x)) :
    (F ⊗ₘ κ).snd = ν.withDensity (fun y => ∫⁻ x, L x y ∂F) := by
  ext s hs
  rw [Measure.snd_compProd, Measure.bind_apply hs κ.measurable.aemeasurable,
    withDensity_apply _ hs,
    lintegral_congr_ae (hκ.mono fun x hx => by rw [hx, withDensity_apply _ hs])]
  exact lintegral_lintegral_swap hL.aemeasurable

/-- **The outcomes of patients with unreported covariates are independent with their marginal
laws.** For `n` patients whose pairs (covariates, outcome) are independent, patient `i` with law
`Fᵢ ⊗ κᵢ`, where `Fᵢ` is a probability law and the Markov kernel `κᵢ` has density `Lᵢ(x, ·)`
with respect to `ν` for `Fᵢ`-almost every `x`, the outcome vector has the product law of the
marginal laws, `ν` with density `y ↦ ∫ Lᵢ(x, y) Fᵢ(dx)`. -/
theorem map_pi_compProd_eq_pi {n : ℕ} (F : Fin n → Measure 𝒳) [∀ i, IsProbabilityMeasure (F i)]
    (ν : Measure 𝒴) [SFinite ν] (κ : Fin n → Kernel 𝒳 𝒴) [∀ i, IsMarkovKernel (κ i)]
    (L : Fin n → 𝒳 → 𝒴 → ℝ≥0∞) (hL : ∀ i, Measurable (Function.uncurry (L i)))
    (hκ : ∀ i, ∀ᵐ x ∂F i, κ i x = ν.withDensity (L i x)) :
    (Measure.pi fun i => F i ⊗ₘ κ i).map (fun z i => (z i).2) =
      Measure.pi fun i => ν.withDensity (fun y => ∫⁻ x, L i x y ∂F i) := by
  have hd : ∀ i, (F i ⊗ₘ κ i).map Prod.snd = ν.withDensity (fun y => ∫⁻ x, L i x y ∂F i) :=
    fun i => snd_compProd_eq_withDensity (F i) ν (κ i) (L i) (hL i) (hκ i)
  rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  simp_rw [hd]

/-- **The outcome vector of patients with unreported covariates has the product of the marginal
densities**: under the hypotheses of `map_pi_compProd_eq_pi` with `ν` σ-finite, the outcome
vector has density `y ↦ ∏ᵢ ∫ Lᵢ(x, yᵢ) Fᵢ(dx)` with respect to `ν ⊗ ⋯ ⊗ ν`. -/
theorem map_pi_compProd_eq_withDensity {n : ℕ} (F : Fin n → Measure 𝒳)
    [∀ i, IsProbabilityMeasure (F i)] (ν : Measure 𝒴) [SigmaFinite ν] (κ : Fin n → Kernel 𝒳 𝒴)
    [∀ i, IsMarkovKernel (κ i)] (L : Fin n → 𝒳 → 𝒴 → ℝ≥0∞)
    (hL : ∀ i, Measurable (Function.uncurry (L i)))
    (hκ : ∀ i, ∀ᵐ x ∂F i, κ i x = ν.withDensity (L i x)) :
    (Measure.pi fun i => F i ⊗ₘ κ i).map (fun z i => (z i).2) =
      (Measure.pi fun _ : Fin n => ν).withDensity (fun y => ∏ i, ∫⁻ x, L i x (y i) ∂F i) := by
  have : ∀ i, IsProbabilityMeasure (ν.withDensity fun y => ∫⁻ x, L i x y ∂F i) := fun i => by
    rw [← snd_compProd_eq_withDensity (F i) ν (κ i) (L i) (hL i) (hκ i)]; infer_instance
  rw [map_pi_compProd_eq_pi F ν κ L hL hκ]
  exact pi_withDensity ν (fun i y => ∫⁻ x, L i x y ∂F i) fun i => (hL i).lintegral_prod_left'

/-- **The law of a summary of an arm with aggregate data**: under the hypotheses of
`map_pi_compProd_eq_withDensity`, a measurable summary `T` of the outcome vector satisfies
`P(T ∈ A) = ∫_{T ∈ A} ∏ᵢ ∫ Lᵢ(x, yᵢ) Fᵢ(dx) d(ν ⊗ ⋯ ⊗ ν)(y)` for every measurable `A`. -/
theorem map_pi_compProd_summary_apply {n : ℕ} (F : Fin n → Measure 𝒳)
    [∀ i, IsProbabilityMeasure (F i)] (ν : Measure 𝒴) [SigmaFinite ν] (κ : Fin n → Kernel 𝒳 𝒴)
    [∀ i, IsMarkovKernel (κ i)] (L : Fin n → 𝒳 → 𝒴 → ℝ≥0∞)
    (hL : ∀ i, Measurable (Function.uncurry (L i)))
    (hκ : ∀ i, ∀ᵐ x ∂F i, κ i x = ν.withDensity (L i x))
    {𝒮 : Type*} [MeasurableSpace 𝒮] {T : (Fin n → 𝒴) → 𝒮} (hT : Measurable T) {A : Set 𝒮}
    (hA : MeasurableSet A) :
    (Measure.pi fun i => F i ⊗ₘ κ i).map (fun z => T fun i => (z i).2) A =
      ∫⁻ y in T ⁻¹' A, ∏ i, ∫⁻ x, L i x (y i) ∂F i ∂(Measure.pi fun _ : Fin n => ν) := by
  have e : (fun z : Fin n → 𝒳 × 𝒴 => T fun i => (z i).2) = T ∘ fun z i => (z i).2 := rfl
  rw [e, ← Measure.map_map hT (by fun_prop), map_pi_compProd_eq_withDensity F ν κ L hL hκ,
    Measure.map_apply hT hA, withDensity_apply _ (hT hA)]

/-- **The density of a discrete summary.** For a finite outcome space with the counting measure
and a summary `T` with values in a space with measurable singletons, the summary takes the value
`s` with probability `∑_{T(y) = s} ∏ᵢ ∫ L(x, yᵢ) F(dx)`. -/
theorem map_pi_compProd_summary_singleton {n : ℕ} [Fintype 𝒴]
    [MeasurableSingletonClass 𝒴] (F : Measure 𝒳) [IsProbabilityMeasure F] (κ : Kernel 𝒳 𝒴)
    [IsMarkovKernel κ] (L : 𝒳 → 𝒴 → ℝ≥0∞) (hL : Measurable (Function.uncurry L))
    (hκ : ∀ᵐ x ∂F, κ x = Measure.count.withDensity (L x)) {𝒮 : Type*} [MeasurableSpace 𝒮]
    [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮] {T : (Fin n → 𝒴) → 𝒮} (hT : Measurable T)
    (s : 𝒮) :
    (Measure.pi fun _ : Fin n => F ⊗ₘ κ).map (fun z => T fun i => (z i).2) {s} =
      ∑ y ∈ Finset.univ.filter (fun y => T y = s), ∏ i, ∫⁻ x, L x (y i) ∂F := by
  have e : (fun z : Fin n → 𝒳 × 𝒴 => T fun i => (z i).2) = T ∘ fun z i => (z i).2 := rfl
  have hset : T ⁻¹' {s} = ↑(Finset.univ.filter fun y => T y = s) := by ext y; simp
  have : IsProbabilityMeasure (Measure.count.withDensity fun y => ∫⁻ x, L x y ∂F) := by
    rw [← snd_compProd_eq_withDensity F Measure.count κ L hL hκ]; infer_instance
  rw [e, ← Measure.map_map hT (by fun_prop),
    map_pi_compProd_eq_pi (fun _ => F) Measure.count (fun _ => κ) (fun _ => L) (fun _ => hL)
      (fun _ => hκ), Measure.map_apply hT (measurableSet_singleton s), hset,
    ← sum_measure_singleton]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Set.univ_pi_singleton, Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (measurableSet_singleton _), Measure.restrict_singleton,
    Measure.count_singleton, one_smul, lintegral_dirac]

/-! ### The number of events of a binary outcome -/

/-- The **binomial mass** `(n choose s) θ^s (1 - θ)^(n - s)` of `s` events among `n` trials with
event probability `θ`. -/
noncomputable def binomialMass (n : ℕ) (θ : ℝ) (s : ℕ) : ℝ :=
  n.choose s * θ ^ s * (1 - θ) ^ (n - s)

/-- The logarithm of the binomial mass is `log (n choose s)` plus the binomial log likelihood
`s log θ + (n - s) log (1 - θ)` of `NetworkMetaAnalysis.binomialLogLik`, for `0 < θ < 1` and
`s ≤ n`. -/
theorem log_binomialMass {n s : ℕ} (hs : s ≤ n) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    Real.log (binomialMass n θ s) =
      Real.log (n.choose s) + NetworkMetaAnalysis.binomialLogLik n s θ := by
  have hc : (0 : ℝ) < n.choose s := by exact_mod_cast Nat.choose_pos hs
  rw [binomialMass, Real.log_mul (by positivity) (pow_pos (by linarith) _).ne',
    Real.log_mul hc.ne' (pow_pos h0 _).ne', Real.log_pow, Real.log_pow,
    NetworkMetaAnalysis.binomialLogLik, Nat.cast_sub hs]
  ring

/-- There are `n choose s` binary vectors of length `n` with exactly `s` entries `true`. -/
theorem card_filter_card_filter_eq (n s : ℕ) :
    (Finset.univ.filter fun y : Fin n → Bool =>
      (Finset.univ.filter fun i => y i = true).card = s).card = n.choose s := by
  have hc : n.choose s = (Finset.powersetCard s (Finset.univ : Finset (Fin n))).card := by
    simp [Finset.card_powersetCard]
  rw [hc]
  refine Finset.card_bij' (fun y _ => Finset.univ.filter fun i => y i = true)
    (fun A _ => fun i => decide (i ∈ A)) ?_ ?_ ?_ ?_
  · intro y hy
    simpa [Finset.mem_powersetCard] using hy
  · intro A hA
    simp only [Finset.mem_powersetCard] at hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    simpa using hA.2
  · intro y _
    funext i
    simp
  · intro A _
    ext i
    simp

/-- A probability law on `{false, true}` with density `q` at `true` and `1 - q` at `false` with
respect to the counting measure has `0 ≤ q ≤ 1`. -/
theorem mem_Icc_of_count_withDensity {q : ℝ} {μ : Measure Bool} [IsProbabilityMeasure μ]
    (h : μ = Measure.count.withDensity fun b => ENNReal.ofReal (if b then q else 1 - q)) :
    0 ≤ q ∧ q ≤ 1 := by
  have h1 := measure_univ (μ := μ)
  rw [h, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count,
    tsum_fintype, Fintype.sum_bool] at h1
  simp only [↓reduceIte, Bool.false_eq_true] at h1
  constructor
  · by_contra hq
    push Not at hq
    rw [ENNReal.ofReal_of_nonpos hq.le, zero_add] at h1
    have := (ENNReal.ofReal_eq_one.mp h1)
    linarith
  · by_contra hq
    push Not at hq
    rw [ENNReal.ofReal_of_nonpos (by linarith : 1 - q ≤ 0), add_zero] at h1
    have := (ENNReal.ofReal_eq_one.mp h1)
    linarith

/-- **The number of events in an arm with aggregate data has the binomial law at the aggregate
event probability.** Let the covariates have the probability law `F`, let the outcome be binary
with event probability `q(x)` given `X = x` (`κ x` has density `q(x)` at `true` and
`1 - q(x)` at `false` with respect to the counting measure, which forces `q(x) ∈ [0, 1]` for
`F`-almost every `x`), and let the pairs of the `n`
patients be independent with law `F ⊗ κ`. Then the number of events takes the value `s` with
probability `(n choose s) θ^s (1 - θ)^(n - s)`, `θ = ∫ q dF`. -/
theorem map_pi_compProd_card_singleton {n : ℕ} (F : Measure 𝒳) [IsProbabilityMeasure F]
    {q : 𝒳 → ℝ} (hq : Measurable q) (κ : Kernel 𝒳 Bool) [IsMarkovKernel κ]
    (hκ : ∀ᵐ x ∂F, κ x = Measure.count.withDensity
      (fun b => ENNReal.ofReal (if b then q x else 1 - q x))) (s : ℕ) :
    (Measure.pi fun _ : Fin n => F ⊗ₘ κ).map
        (fun z => (Finset.univ.filter fun i => (z i).2 = true).card) {s} =
      ENNReal.ofReal (binomialMass n (∫ x, q x ∂F) s) := by
  set L : 𝒳 → Bool → ℝ≥0∞ := fun x b => ENNReal.ofReal (if b then q x else 1 - q x) with hLdef
  have hL : Measurable (Function.uncurry L) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.ite ?_ (hq.comp measurable_fst)
      (measurable_const.sub (hq.comp measurable_fst)))
    exact measurableSet_eq_fun measurable_snd measurable_const
  have hq01 : ∀ᵐ x ∂F, 0 ≤ q x ∧ q x ≤ 1 := hκ.mono fun x hx => mem_Icc_of_count_withDensity hx
  have hq0 : ∀ᵐ x ∂F, 0 ≤ q x := hq01.mono fun x hx => hx.1
  have hq1 : ∀ᵐ x ∂F, q x ≤ 1 := hq01.mono fun x hx => hx.2
  have hqi : Integrable q F := Integrable.of_bound hq.aestronglyMeasurable 1
    (hq01.mono fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2)
  set θ := ∫ x, q x ∂F with hθ
  have hint : ∀ b : Bool, ∫⁻ x, L x b ∂F = ENNReal.ofReal (if b then θ else 1 - θ) := by
    intro b
    cases b
    · simp only [hLdef, Bool.false_eq_true, ↓reduceIte]
      have hi1 : Integrable (fun x => 1 - q x) F := (integrable_const 1).sub hqi
      rw [← ofReal_integral_eq_lintegral_ofReal hi1
        (hq1.mono fun x hx => by simp [hx]), integral_sub (integrable_const 1)
        hqi, integral_const, probReal_univ, one_smul]
    · simp only [hLdef, ↓reduceIte]
      rw [← ofReal_integral_eq_lintegral_ofReal hqi hq0]
  have hθ0 : 0 ≤ θ := integral_nonneg_of_ae hq0
  have hθ1 : θ ≤ 1 := by
    calc θ ≤ ∫ _x, (1 : ℝ) ∂F := integral_mono_ae hqi (integrable_const 1) hq1
      _ = 1 := by simp
  refine (map_pi_compProd_summary_singleton F κ L hL hκ
    (T := fun y : Fin n → Bool => (Finset.univ.filter fun i => y i = true).card)
    (measurable_of_finite _) s).trans ?_
  have hprod : ∀ y ∈ Finset.univ.filter (fun y : Fin n → Bool =>
      (Finset.univ.filter fun i => y i = true).card = s),
      ∏ i, ∫⁻ x, L x (y i) ∂F = ENNReal.ofReal (θ ^ s * (1 - θ) ^ (n - s)) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp_rw [hint, apply_ite ENNReal.ofReal]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hy,
      ENNReal.ofReal_mul (pow_nonneg hθ0 _), ENNReal.ofReal_pow hθ0,
      ENNReal.ofReal_pow (by linarith)]
    congr 2
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => y i = true)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    simp only [Bool.not_eq_true]
    have e : (Finset.univ.filter fun i => y i = false) =
        (Finset.univ.filter fun i => ¬ y i = true) := by
      ext i; simp
    rw [e]
    omega
  rw [Finset.sum_congr rfl hprod, Finset.sum_const, card_filter_card_filter_eq, nsmul_eq_mul,
    binomialMass, mul_assoc, ENNReal.ofReal_mul (p := (n.choose s : ℝ)) (by positivity),
    ENNReal.ofReal_natCast]

end NetworkMetaRegression

end CausalInference
