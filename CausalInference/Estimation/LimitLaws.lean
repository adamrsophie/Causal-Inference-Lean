/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.ContinuousMapping
public import CausalInference.Estimation.ZEstimatorExamples

/-!
# Limit laws: Slutsky, tightness and the delta method in distribution

Convergence in distribution of a sequence `X n` of random variables on one probability space is
`MeasureTheory.TendstoInDistribution X atTop Y (fun _ ↦ μ) P'`, with the limit `Y` a random
variable on some probability space `P'`; its law is fixed with `ProbabilityTheory.HasLaw`.

## Main results

* `MeasureTheory.TendstoInDistribution.of_hasLaw`: the limit variable may be replaced by any
  variable with the same law.
* `MeasureTheory.TendstoInDistribution.div_tendstoInMeasure_const`: Slutsky's theorem for a
  quotient by a sequence converging in probability to a nonzero constant.
* `MeasureTheory.TendstoInDistribution.boundedInProbability`: a sequence converging in
  distribution in a normed space is bounded in probability.
* `MeasureTheory.TendstoInDistribution.delta_method`: the delta method for any limit law in normed
  spaces: if `√n (T n - θ) → Y` in distribution and `g` is differentiable at `θ`, then
  `√n (g (T n) - g θ) → Dg Y`.
* `MeasureTheory.TendstoInDistribution.delta_method_real`: the scalar case with a centered
  Gaussian limit.
* Instances in which every hypothesis is checked:
  `CausalInference.exp_sampleMean_tendstoInDistribution` (the delta method for the exponential of a
  sample mean) and
  `CausalInference.sqrt_mul_sampleMean_sub_div_sampleMean_tendstoInDistribution` (Slutsky's
  quotient).

The other forms of Slutsky's theorem are in Mathlib:
`MeasureTheory.TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const` (a
continuous function of the pair),
`MeasureTheory.TendstoInDistribution.add_of_tendstoInMeasure_const` (a sum), and
`MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub` (a perturbation tending to zero in
probability).

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, Lemma 2.8 (Slutsky), Theorem 2.4
(tightness) and Theorem 3.1 (the delta method).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace CausalInference

section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Change of the limit variable.** If `X n → Y` in distribution and `Y'` (on any probability
space) has the same law `ν` as `Y`, then `X n → Y'` in distribution. -/
theorem _root_.MeasureTheory.TendstoInDistribution.of_hasLaw
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : ℕ → Ω → E} {Y : Ω' → E}
    (h : TendstoInDistribution X atTop Y (fun _ ↦ μ) P') {ν : Measure E} (hY : HasLaw Y ν P')
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {Y' : Ω'' → E} (hY' : HasLaw Y' ν P'') :
    TendstoInDistribution X atTop Y' (fun _ ↦ μ) P'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hY'.aemeasurable
  tendsto := by
    have he : (⟨P''.map Y', inferInstance⟩ : ProbabilityMeasure E) =
        ⟨P'.map Y, inferInstance⟩ :=
      Subtype.ext (by simp [hY.map_eq, hY'.map_eq])
    rw [he]
    exact h.tendsto

/-- **Slutsky's theorem for a quotient.** If real `X n → Z` in distribution and `Y n → c ≠ 0` in
probability with each `Y n` almost everywhere measurable, then `X n / Y n → Z / c` in
distribution. -/
theorem _root_.MeasureTheory.TendstoInDistribution.div_tendstoInMeasure_const
    {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hc : c ≠ 0) (hX : TendstoInDistribution X atTop Z (fun _ ↦ μ) P')
    (hY : TendstoInMeasure μ Y atTop (fun _ ↦ c)) (hYm : ∀ n, AEMeasurable (Y n) μ) :
    TendstoInDistribution (fun n ω ↦ X n ω / Y n ω) atTop (fun ω ↦ Z ω / c) (fun _ ↦ μ) P' := by
  have hinv := hY.inv_of_ne_zero hYm hc
  simpa only [div_eq_mul_inv] using hX.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ ↦ p.1 * p.2) continuous_mul hinv fun n ↦ (hYm n).inv

/-- **Tightness of a sequence converging in distribution.** In a normed space, a sequence
converging in distribution is bounded in probability (in norm). The closed sets
`{x | k + 1 ≤ ‖x‖}` decrease to the empty set, so their mass under the limit law becomes small,
and the portmanteau theorem bounds the `limsup` of their masses under the laws of `X n`. -/
theorem _root_.MeasureTheory.TendstoInDistribution.boundedInProbability
    {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {X : ℕ → Ω → E} {Y : Ω' → E}
    (h : TendstoInDistribution X atTop Y (fun _ ↦ μ) P') :
    BoundedInProbability μ (fun n ω ↦ ‖X n ω‖) := by
  intro ε hε
  let C : ℕ → Set E := fun k ↦ {x | (k : ℝ) + 1 ≤ ‖x‖}
  have hCc : ∀ k, IsClosed (C k) := fun k ↦ isClosed_le continuous_const continuous_norm
  have hC : Tendsto (fun k ↦ (P'.map Y) (C k)) atTop (𝓝 0) := by
    have hanti : Antitone C := fun i j hij x hx ↦
      le_trans (by gcongr) (show (j : ℝ) + 1 ≤ ‖x‖ from hx)
    have := tendsto_measure_iInter_atTop (μ := P'.map Y)
      (fun k ↦ (hCc k).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    have hempty : ⋂ k, C k = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall, not_le, C,
        Set.mem_ofPred_eq]
      obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
      exact ⟨k, by linarith⟩
    rwa [hempty, measure_empty] at this
  obtain ⟨k, hk⟩ := (hC.eventually (gt_mem_nhds hε)).exists
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto (hCc k)
  have hev := eventually_lt_of_limsup_lt (hlim.trans_lt hk)
  refine ⟨(k : ℝ) + 1, by positivity, hev.mono fun n hn ↦ ?_⟩
  simp only [ProbabilityMeasure.coe_mk] at hn
  rw [Measure.map_apply₀ (h.forall_aemeasurable n)
    (hCc k).measurableSet.nullMeasurableSet] at hn
  refine le_of_eq_of_le ?_ hn.le
  congr 1
  ext ω
  simp [C]

/-- **The delta method for any limit law.** Let `E, F` be normed spaces (`F` second countable),
`√n (T n - θ) → Y` in distribution, and `g` differentiable at `θ` with derivative `Dg`. If each
`√n (g (T n) - g θ)` is almost everywhere measurable, then `√n (g (T n) - g θ) → Dg Y` in
distribution. The scaled error is bounded in probability and the first order remainder is
`o(‖t - θ‖)`, so the scaled remainder tends to zero in probability. -/
theorem _root_.MeasureTheory.TendstoInDistribution.delta_method
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {T : ℕ → Ω → E} {θ : E}
    {Y : Ω' → E} (hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (T n ω - θ)) atTop Y
      (fun _ ↦ μ) P') {g : E → F} {Dg : E →L[ℝ] F} (hg : HasFDerivAt g Dg θ)
    (hgm : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) • (g (T n ω) - g θ)) μ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (g (T n ω) - g θ)) atTop (fun ω ↦ Dg (Y ω))
      (fun _ ↦ μ) P' := by
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ (hT.continuous_comp Dg.continuous) ?_
    hgm
  have hXb := hT.boundedInProbability
  refine tendstoInMeasure_of_good_events fun ε hε κ hκ ↦ ?_
  obtain ⟨K, hK, hXK⟩ := hXb.exists_norm_lt hκ
  obtain ⟨δ, hδ, hloc⟩ := Metric.eventually_nhds_iff.1
    (hg.isLittleO.def (show 0 < ε / (2 * K) by positivity))
  have hn : ∀ᶠ n : ℕ in atTop, K < δ * √(n : ℝ) :=
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hδ).eventually_gt_atTop K
  refine ⟨_, hXK, ?_⟩
  filter_upwards [hn] with n hn ω hω
  change ‖√(n : ℝ) • (T n ω - θ)‖ < K at hω
  have hs : 0 < √(n : ℝ) := by
    rcases eq_or_lt_of_le (Real.sqrt_nonneg (n : ℝ)) with h0 | h0
    · rw [← h0, mul_zero] at hn; exact absurd hn (not_lt.2 hK.le)
    · exact h0
  rw [norm_smul, Real.norm_of_nonneg hs.le] at hω
  have hTθ : dist (T n ω) θ < δ := by
    rw [dist_eq_norm]
    by_contra hcon
    replace hcon := not_lt.1 hcon
    have : √(n : ℝ) * δ ≤ √(n : ℝ) * ‖T n ω - θ‖ := mul_le_mul_of_nonneg_left hcon hs.le
    linarith [mul_comm δ √(n : ℝ)]
  have hb := hloc hTθ
  change dist (√(n : ℝ) • (g (T n ω) - g θ) - Dg (√(n : ℝ) • (T n ω - θ))) 0 < ε
  rw [dist_zero_right, map_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hs.le]
  calc √(n : ℝ) * ‖g (T n ω) - g θ - Dg (T n ω - θ)‖
      ≤ √(n : ℝ) * (ε / (2 * K) * ‖T n ω - θ‖) := mul_le_mul_of_nonneg_left hb hs.le
    _ = ε / (2 * K) * (√(n : ℝ) * ‖T n ω - θ‖) := by ring
    _ ≤ ε / (2 * K) * K := mul_le_mul_of_nonneg_left hω.le (by positivity)
    _ < ε := by field_simp; linarith

/-- **The delta method, scalar Gaussian case.** If `√n (T n - θ) → N(0, v)` in distribution (the
limit `Y` has this law), `g` has derivative `d` at `θ`, and each `√n (g (T n) - g θ)` is almost
everywhere measurable, then `√n (g (T n) - g θ)` converges in distribution to every variable `Y'`
with law `N(0, d² v)`. -/
theorem _root_.MeasureTheory.TendstoInDistribution.delta_method_real
    {T : ℕ → Ω → ℝ} {θ : ℝ} {v : ℝ≥0}
    {Y : Ω' → ℝ} (hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (T n ω - θ)) atTop Y
      (fun _ ↦ μ) P') (hY : HasLaw Y (gaussianReal 0 v) P') {g : ℝ → ℝ} {d : ℝ}
    (hg : HasDerivAt g d θ) (hgm : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) * (g (T n ω) - g θ)) μ)
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {Y' : Ω'' → ℝ} (hY' : HasLaw Y' (gaussianReal 0 (⟨d ^ 2, sq_nonneg d⟩ * v)) P'') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (g (T n ω) - g θ)) atTop Y'
      (fun _ ↦ μ) P'' := by
  have h := TendstoInDistribution.delta_method (T := T) (θ := θ) (Y := Y)
    (by simpa only [smul_eq_mul] using hT) hg.hasFDerivAt
    (by simpa only [smul_eq_mul] using hgm)
  have hlaw : HasLaw (fun ω ↦ d * Y ω) (gaussianReal 0 (⟨d ^ 2, sq_nonneg d⟩ * v)) P' := by
    have := gaussianReal_const_mul hY d
    rw [mul_zero] at this
    exact this
  have h' : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (g (T n ω) - g θ)) atTop
      (fun ω ↦ d * Y ω) (fun _ ↦ μ) P' := by
    simpa [smul_eq_mul, mul_comm] using h
  exact h'.of_hasLaw hlaw hY'

end

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}

/-- **Instance of the delta method: the exponential of a sample mean.** For an i.i.d. sample, a
measurable `f` with `f (O 0)` square integrable, mean `m` and variance `σ²`, the central limit
theorem gives `√n (P_n f - m) → N(0, σ²)`, and `exp` has derivative `exp m` at `m`. Hence
`√n (exp (P_n f) - exp m)` converges in distribution to every variable with law
`N(0, exp(m)² σ²)`. -/
theorem exp_sampleMean_tendstoInDistribution (hO : IsIIDSample O μ) {f : 𝒪 → ℝ}
    (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0
      (⟨Real.exp (μ[fun ω ↦ f (O 0 ω)]) ^ 2, sq_nonneg _⟩ *
        (μ[fun ω ↦ (f (O 0 ω) - μ[fun ω ↦ f (O 0 ω)]) ^ 2]).toNNReal)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) * (Real.exp (sampleMean f O n ω) - Real.exp (μ[fun ω ↦ f (O 0 ω)])))
      atTop Y (fun _ ↦ μ) P' := by
  set m := μ[fun ω ↦ f (O 0 ω)]
  have hmeas : ∀ n, AEMeasurable (sampleMean f O n) μ :=
    (isSampleMeasurable_sampleMean hf O).aemeasurable hO
  have hclt := (sampleMean_isAsymptoticallyLinear hf hf2).tendstoInDistribution hO hmeas
    (HasLaw.id (μ := gaussianReal 0 (μ[fun ω ↦ (f (O 0 ω) - m) ^ 2]).toNNReal))
  refine hclt.delta_method_real HasLaw.id (Real.hasDerivAt_exp m) (fun n ↦ ?_) hY
  exact aemeasurable_const.mul ((Real.measurable_exp.comp_aemeasurable (hmeas n)).sub_const _)

/-- **Instance of Slutsky's theorem for a quotient: a scaled error over a sample mean.** For an
i.i.d. sample, measurable `f, g` with `f (O 0)` square integrable, `g (O 0)` integrable and
`E g (O 0) ≠ 0`, the quotient `√n (P_n f - E f (O 0)) / P_n g` converges in distribution to
`Y / E g (O 0)` for every `Y` with law `N(0, Var f (O 0))`. -/
theorem sqrt_mul_sampleMean_sub_div_sampleMean_tendstoInDistribution (hO : IsIIDSample O μ)
    {f g : 𝒪 → ℝ} (hf : Measurable f) (hg : Measurable g) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    (hg1 : Integrable (fun ω ↦ g (O 0 ω)) μ) (hgne : μ[fun ω ↦ g (O 0 ω)] ≠ 0)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0
      (μ[fun ω ↦ (f (O 0 ω) - μ[fun ω ↦ f (O 0 ω)]) ^ 2]).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) * (sampleMean f O n ω - μ[fun ω ↦ f (O 0 ω)]) / sampleMean g O n ω) atTop
      (fun ω ↦ Y ω / μ[fun ω ↦ g (O 0 ω)]) (fun _ ↦ μ) P' :=
  ((sampleMean_isAsymptoticallyLinear hf hf2).tendstoInDistribution hO
    ((isSampleMeasurable_sampleMean hf O).aemeasurable hO) hY).div_tendstoInMeasure_const hgne
    (sampleMean_isConsistent hO hg hg1) ((isSampleMeasurable_sampleMean hg O).aemeasurable hO)

end CausalInference
