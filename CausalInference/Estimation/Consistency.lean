/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Estimator
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Moments.Variance

/-!
# Consistency of estimators

An estimator sequence `θhat : ℕ → Ω → ℝ` is consistent for `θ` when `θhat n` converges to `θ` in
probability, that is `MeasureTheory.TendstoInMeasure μ θhat atTop (fun _ ↦ θ)`.

Main results:

* `MeasureTheory.TendstoInMeasure.add`, `MeasureTheory.TendstoInMeasure.neg`,
  `MeasureTheory.TendstoInMeasure.sub`, `MeasureTheory.TendstoInMeasure.const_mul`,
  `MeasureTheory.TendstoInMeasure.of_norm_le` and its almost everywhere form
  `MeasureTheory.TendstoInMeasure.of_norm_le_ae`: closure properties of convergence in
  probability, which the pinned Mathlib does not provide. They are declared in the namespace of
  `MeasureTheory.TendstoInMeasure`, so dot notation `hf.add hg` applies.
* `CausalInference.sampleMean_isConsistent`: the sample mean of an integrable `f (O i)` from an
  i.i.d. sample is consistent for `E f (O 0)` (strong law of large numbers, then almost sure
  convergence implies convergence in probability).
* `CausalInference.IsConsistent.comp`, `CausalInference.IsConsistent.comp₂`,
  `CausalInference.IsConsistent.mul`: continuous mapping and product rule for consistency.
* `CausalInference.sampleSD_isConsistent`: the plug-in sample standard deviation
  `√(P_n f² - (P_n f)²)` is consistent for the population standard deviation.

Source: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapters 2 and 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

section TendstoInMeasure

variable {ι E : Type*} [SeminormedAddCommGroup E] {μ : Measure Ω} {l : Filter ι}
  {f f' : ι → Ω → E} {g g' : Ω → E}

/-- Convergence in measure is preserved by sums: if `f i → g` and `f' i → g'` in measure, then
`f i + f' i → g + g'` in measure. -/
theorem _root_.MeasureTheory.TendstoInMeasure.add (hf : TendstoInMeasure μ f l g)
    (hf' : TendstoInMeasure μ f' l g') :
    TendstoInMeasure μ (fun i ↦ f i + f' i) l (g + g') := by
  rw [tendstoInMeasure_iff_norm] at hf hf' ⊢
  intro ε hε
  have h := (hf (ε / 2) (by positivity)).add (hf' (ε / 2) (by positivity))
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le) ?_
  intro i
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro x hx
  simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.add_apply] at hx ⊢
  by_contra! hcon
  have : ‖f i x + f' i x - (g x + g' x)‖ ≤ ‖f i x - g x‖ + ‖f' i x - g' x‖ := by
    rw [add_sub_add_comm]
    exact norm_add_le _ _
  linarith

/-- Convergence in measure is preserved by negation. -/
theorem _root_.MeasureTheory.TendstoInMeasure.neg (hf : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i ↦ -f i) l (-g) := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  intro ε hε
  simpa only [Pi.neg_apply, neg_sub_neg, norm_sub_rev] using hf ε hε

/-- Convergence in measure is preserved by differences. -/
theorem _root_.MeasureTheory.TendstoInMeasure.sub (hf : TendstoInMeasure μ f l g)
    (hf' : TendstoInMeasure μ f' l g') :
    TendstoInMeasure μ (fun i ↦ f i - f' i) l (g - g') := by
  simpa [sub_eq_add_neg] using hf.add hf'.neg

/-- Domination almost everywhere: if `f i → 0` in measure and eventually `‖h i ω‖ ≤ ‖f i ω‖` for
almost every `ω`, then `h i → 0` in measure. -/
theorem _root_.MeasureTheory.TendstoInMeasure.of_norm_le_ae {h : ι → Ω → E}
    (hf : TendstoInMeasure μ f l 0) (hle : ∀ᶠ i in l, ∀ᵐ ω ∂μ, ‖h i ω‖ ≤ ‖f i ω‖) :
    TendstoInMeasure μ h l 0 := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf ε hε)
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hle] with i hi
  refine measure_mono_ae ?_
  filter_upwards [hi] with x hx hmem
  simp only [Pi.zero_apply, sub_zero] at hmem ⊢
  exact hmem.trans hx

/-- Domination: if `f i → 0` in measure and eventually `‖h i ω‖ ≤ ‖f i ω‖` for every `ω`, then
`h i → 0` in measure. -/
theorem _root_.MeasureTheory.TendstoInMeasure.of_norm_le {h : ι → Ω → E}
    (hf : TendstoInMeasure μ f l 0) (hle : ∀ᶠ i in l, ∀ ω, ‖h i ω‖ ≤ ‖f i ω‖) :
    TendstoInMeasure μ h l 0 :=
  hf.of_norm_le_ae (hle.mono fun _ hi ↦ Eventually.of_forall hi)

/-- Convergence in measure is preserved by multiplication on the left by a constant: if
`u i → v` in measure, then `c * u i → c * v` in measure. -/
theorem _root_.MeasureTheory.TendstoInMeasure.const_mul {R : Type*} [SeminormedRing R]
    {u : ι → Ω → R} {v : Ω → R} (c : R) (hu : TendstoInMeasure μ u l v) :
    TendstoInMeasure μ (fun i ω ↦ c * u i ω) l (fun ω ↦ c * v ω) := by
  rw [tendstoInMeasure_iff_norm] at hu ⊢
  intro ε hε
  have hc : 0 < ‖c‖ + 1 := by positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hu (ε / (‖c‖ + 1)) (by positivity)) (fun _ ↦ zero_le) fun i ↦ measure_mono fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  by_contra! hlt
  have h1 : ‖c * u i x - c * v x‖ ≤ ‖c‖ * ‖u i x - v x‖ := by
    rw [← mul_sub]
    exact norm_mul_le _ _
  have h2 : (‖c‖ + 1) * ‖u i x - v x‖ < ε := by rwa [lt_div_iff₀' hc] at hlt
  nlinarith [norm_nonneg (u i x - v x)]

end TendstoInMeasure

/-- The estimator sequence `θhat` is consistent for `θ` under `μ`: `θhat n` converges to `θ` in
probability. -/
def IsConsistent (θhat : ℕ → Ω → ℝ) (θ : ℝ) (μ : Measure Ω) : Prop :=
  TendstoInMeasure μ θhat atTop (fun _ ↦ θ)

/-- **Weak law of large numbers for the sample mean.** If `O` is an i.i.d. sample under a
probability measure `μ`, `f` is measurable and `f (O 0)` is integrable, then the sample mean
`n⁻¹ ∑_{i < n} f (O i)` is consistent for `E f (O 0)`. The proof goes through the strong law of
large numbers (`ProbabilityTheory.strong_law_ae_real`) and the fact that almost sure convergence
implies convergence in probability on a finite measure space. -/
theorem sampleMean_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hint : Integrable (fun ω ↦ f (O 0 ω)) μ) :
    IsConsistent (sampleMean f O) (μ[fun ω ↦ f (O 0 ω)]) μ := by
  have hslln := strong_law_ae_real (fun i ω ↦ f (O i ω)) hint (hO.pairwise_indepFun hf)
    (hO.comp hf).ident
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
  · exact ((isSampleMeasurable_sampleMean hf O).aemeasurable hO n).aestronglyMeasurable
  · filter_upwards [hslln] with ω hω
    simpa [sampleMean, div_eq_inv_mul] using hω

namespace IsConsistent

variable {μ : Measure Ω}

/-- **Continuous mapping for consistency.** If `θhat` is consistent for `θ` and `g` is continuous
at `θ`, then `g ∘ θhat` is consistent for `g θ`. No measurability of `g` is needed. -/
theorem comp {θhat : ℕ → Ω → ℝ} {θ : ℝ} {g : ℝ → ℝ} (hg : ContinuousAt g θ)
    (h : IsConsistent θhat θ μ) : IsConsistent (fun n ω ↦ g (θhat n ω)) (g θ) μ := by
  rw [IsConsistent, tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hg ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
    (fun _ ↦ zero_le) fun n ↦ measure_mono fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  by_contra! hlt
  exact absurd (hδg hlt) (not_lt.2 hx)

/-- **Joint continuous mapping for consistency.** If `a` is consistent for `α`, `b` is consistent
for `β`, and `(x, y) ↦ g x y` is continuous at `(α, β)`, then `g a b` is consistent for
`g α β`. -/
theorem comp₂ {a b : ℕ → Ω → ℝ} {α β : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : ContinuousAt (Function.uncurry g) (α, β)) (ha : IsConsistent a α μ)
    (hb : IsConsistent b β μ) : IsConsistent (fun n ω ↦ g (a n ω) (b n ω)) (g α β) μ := by
  rw [IsConsistent, tendstoInMeasure_iff_dist] at ha hb ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hg ε hε
  have hsum := (ha δ hδ).add (hb δ hδ)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    fun n ↦ (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
  by_contra! hlt
  have hd : dist (a n x, b n x) (α, β) < δ := by
    rw [Prod.dist_eq]
    exact max_lt hlt.1 hlt.2
  exact absurd (hδg hd) (not_lt.2 hx)

/-- **Product rule for consistency.** If `a` is consistent for `α` and `b` is consistent for `β`,
then `a * b` is consistent for `α * β`. -/
theorem mul {a b : ℕ → Ω → ℝ} {α β : ℝ} (ha : IsConsistent a α μ) (hb : IsConsistent b β μ) :
    IsConsistent (fun n ω ↦ a n ω * b n ω) (α * β) μ :=
  comp₂ (g := (· * ·)) continuous_mul.continuousAt ha hb

end IsConsistent

/-- The plug-in sample standard deviation `√(n⁻¹ ∑_{i < n} f (O i)² - (n⁻¹ ∑_{i < n} f (O i))²)`
of the transformed observations `f (O i)`. At `n = 0` it takes the value `0`. -/
noncomputable def sampleSD (f : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : ℝ :=
  √(sampleMean (fun x ↦ f x ^ 2) O n ω - sampleMean f O n ω ^ 2)

/-- The sample standard deviation of a measurable transformation is a measurable function of the
first `n` observations. -/
theorem isSampleMeasurable_sampleSD {f : 𝒪 → ℝ} (hf : Measurable f) (O : ℕ → Ω → 𝒪) :
    IsSampleMeasurable (sampleSD f O) O := by
  intro n
  obtain ⟨g₁, hg₁, h₁⟩ := isSampleMeasurable_sampleMean (hf.pow_const 2) O n
  obtain ⟨g₂, hg₂, h₂⟩ := isSampleMeasurable_sampleMean hf O n
  refine ⟨fun x ↦ √(g₁ x - g₂ x ^ 2), by fun_prop, ?_⟩
  funext ω
  simp only [sampleSD, congrFun h₁ ω, congrFun h₂ ω]

/-- **Consistency of the sample standard deviation.** If `O` is an i.i.d. sample under a
probability measure `μ`, `f` is measurable and `f (O 0)` has a finite second moment, then the
sample standard deviation of `f (O i)` is consistent for the population standard deviation
`√(Var f (O 0))`. The proof combines the laws of large numbers for `f` and `f²` with the joint
continuous mapping lemma for `(a, b) ↦ √(a - b²)`. -/
theorem sampleSD_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ) :
    IsConsistent (sampleSD f O) (√(Var[fun ω ↦ f (O 0 ω); μ])) μ := by
  have h1 := sampleMean_isConsistent hO (hf.pow_const 2) hf2.integrable_sq
  have h2 := sampleMean_isConsistent hO hf (hf2.integrable one_le_two)
  have hg : Continuous (Function.uncurry fun a b : ℝ ↦ √(a - b ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_fst.sub (continuous_snd.pow 2))
  have h3 := h1.comp₂ hg.continuousAt h2
  have hX : (fun ω ↦ f (O 0 ω)) ^ 2 = fun ω ↦ f (O 0 ω) ^ 2 := by
    ext ω
    simp only [Pi.pow_apply]
  rw [variance_eq_sub hf2, hX]
  exact h3

end CausalInference
