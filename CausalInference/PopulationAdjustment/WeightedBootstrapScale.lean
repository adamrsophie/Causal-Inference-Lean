/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapExamplesMatched

/-!
# Bootstrap coverage on the log and logit scales

**The delta method for bootstrap linearity** (`IsBootstrapLinear.comp_hasStrictDerivAt`): if a
statistic `T` is bootstrap linear with influence function `ψ`, its data estimate `T̂ₙ` is
consistent for `θ`, and `g` has the strict derivative `g'` at `θ`, then `g ∘ T` is bootstrap
linear with influence function `g' ψ`. The proof writes the bootstrap remainder of `g ∘ T` as
`√n (g(T*) - g(T̂) - g' (T* - T̂)) + g' R`, where `R` is the remainder of `T`; the first term is
at most `ε |√n (T* - T̂)|` once `T*` and `T̂` are close to `θ`, and `√n (T* - T̂)` is bounded in
conditional probability, in probability.

The coverage theorems for the weighted arm mean on the log scale (`m₀ > 0`) and on the logit
scale (`0 < m₀ < 1`) follow, under the model primitives of the asymptotic normality theorem and
a positive variance. In the two coin model with one matched feature the intervals cover
`log m₀ = log 2` in the treated arm and `logit m₀ = 0` in the control arm.

## Main results

* `IsBootstrapLinear.resampleTendstoZero`: bootstrap linearity in the order calculus.
* `ResampleTendstoZero.of_le_mul`: a term dominated by `ε` times a bounded term.
* `tendstoInMeasure_of_isAsymptoticallyLinear`: asymptotic linearity gives consistency.
* `IsBootstrapLinear.comp_hasStrictDerivAt`: the delta method for bootstrap linearity.
* `tendsto_bootstrapArmMean_log_coverage`, `tendsto_bootstrapArmMean_logit_coverage`.
* `example_bootstrap_log_coverage_true`, `example_bootstrap_logit_coverage_false`.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, Cambridge University Press, chapter 23.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix Set
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment Bootstrap IndirectComparison

section General

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {P : Measure Ω}
  {O : ℕ → Ω → 𝒪}

/-- **Bootstrap linearity in the order calculus**: the bootstrap remainder tends to zero in
conditional probability, in probability. -/
theorem IsBootstrapLinear.resampleTendstoZero {T : (n : ℕ) → (Fin n → 𝒪) → ℝ} {ψ : 𝒪 → ℝ}
    (h : IsBootstrapLinear P O T ψ) :
    ResampleTendstoZero P O fun n ω y => bootstrapRemainder T ψ O n ω y := by
  intro ε hε κ hκ
  have h1 := (tendstoInMeasure_iff_dist.1 (h ε hε)) κ hκ
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 h1) _ (ENNReal.ofReal_pos.2 hκ)] with n hn
  refine (measure_mono fun ω hω => ?_).trans hn
  simp only [Set.mem_ofPred_eq, not_lt] at hω ⊢
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  exact hω

variable {X Y : (n : ℕ) → Ω → (Fin n → 𝒪) → ℝ}

/-- **A term dominated by `ε` times a bounded term** tends to zero. -/
theorem ResampleTendstoZero.of_le_mul (hY : ResampleBounded P O Y)
    (h : ∀ ε : ℝ, 0 < ε → ResampleEventually P O fun n ω y => |X n ω y| ≤ ε * |Y n ω y|) :
    ResampleTendstoZero P O X := fun ε₀ hε₀ κ hκ => by
  obtain ⟨K, hK⟩ := hY (κ / 2) (by positivity)
  have hε : 0 < ε₀ / (|K| + 1) := by positivity
  refine ((h _ hε (κ / 2) (by positivity)).and hK (by positivity) (by positivity)).mono
    (fun n ω y ⟨h1, h2⟩ => ?_) (by linarith)
  have h3 : |Y n ω y| ≤ |K| := h2.trans (le_abs_self K)
  have h4 : ε₀ / (|K| + 1) * |K| < ε₀ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg K]
  calc |X n ω y| ≤ ε₀ / (|K| + 1) * |Y n ω y| := h1
    _ ≤ ε₀ / (|K| + 1) * |K| := mul_le_mul_of_nonneg_left h3 hε.le
    _ < ε₀ := h4

/-- `(√n)⁻¹ → 0`. -/
theorem eventually_inv_sqrt_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (√(n : ℝ))⁻¹ < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 / ε) ^ 2)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hlt : 1 / ε < √(n : ℝ) :=
    (Real.lt_sqrt (by positivity)).2 (hN.trans_le (by exact_mod_cast hn))
  rw [inv_lt_comm₀ ((by positivity : (0 : ℝ) < 1 / ε).trans hlt) hε]
  rwa [one_div] at hlt

theorem resampleTendstoZero_inv_sqrt :
    ResampleTendstoZero P O fun n (_ : Ω) (_ : Fin n → 𝒪) => (√(n : ℝ))⁻¹ := fun ε hε =>
  ResampleEventually.of_eventually ((eventually_inv_sqrt_lt hε).mono fun n hn _ _ => by
    rwa [abs_of_nonneg (by positivity)])

/-- A term `√n Z` bounded in conditional probability makes `Z` small. -/
theorem ResampleBounded.resampleTendstoZero_of_sqrt_mul
    (h : ResampleBounded P O fun n ω y => √(n : ℝ) * X n ω y) : ResampleTendstoZero P O X :=
  (resampleTendstoZero_inv_sqrt.mul_bounded h).of_le (ResampleEventually.of_eventually
    ((eventually_ge_atTop 1).mono fun n hn ω y => by
      have : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
      rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]))

/-- **Asymptotic linearity gives consistency**: `θ̂ₙ → θ` in probability. -/
theorem tendstoInMeasure_of_isAsymptoticallyLinear [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {θhat : ℕ → Ω → ℝ} {θ : ℝ} {φ : 𝒪 → ℝ}
    (h : IsAsymptoticallyLinear θhat θ φ O P) :
    TendstoInMeasure P θhat atTop (fun _ => θ) := by
  have hX : TendstoInMeasure P (fun (n : ℕ) (_ : Ω) => (√(n : ℝ))⁻¹) atTop 0 := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_inv_sqrt_lt hε] with n hn
    have : {ω : Ω | ε ≤ dist ((√(n : ℝ))⁻¹) ((0 : Ω → ℝ) ω)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le, Pi.zero_apply,
        Real.dist_eq, sub_zero]
      rwa [abs_of_nonneg (by positivity)]
    rw [this, measure_empty]
  have hXY := tendstoInMeasure_mul_of_bounded hX (h.sqrt_mul_sub_boundedInProbability hO)
  rw [tendstoInMeasure_iff_dist] at hXY ⊢
  intro ε hε
  refine (hXY ε hε).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hsq : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, Real.dist_eq, sub_zero]
  rw [← mul_assoc, inv_mul_cancel₀ hsq.ne', one_mul]

omit mΩ [MeasurableSpace 𝒪] in
theorem sampleMean_const_mul (c : ℝ) (f : 𝒪 → ℝ) (n : ℕ) (ω : Ω) :
    sampleMean (fun z => c * f z) O n ω = c * sampleMean f O n ω := by
  simp only [sampleMean, ← Finset.mul_sum]
  ring

/-- **The delta method for bootstrap linearity.** Let `O` be an i.i.d. sample, `T` bootstrap
linear with a measurable square integrable influence function `ψ`, the data estimate `T̂ₙ`
consistent for `θ`, and `g` with strict derivative `g'` at
`θ`. Then `g ∘ T` is bootstrap linear with influence function `g' ψ`. -/
theorem IsBootstrapLinear.comp_hasStrictDerivAt [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {T : (n : ℕ) → (Fin n → 𝒪) → ℝ} {ψ : 𝒪 → ℝ} (hlin : IsBootstrapLinear P O T ψ)
    (hψ : Measurable ψ) (hψ2 : MemLp ψ 2 (P.map (O 0))) {θ : ℝ}
    (hθ' : TendstoInMeasure P (fun n ω => T n (dataPrefix O n ω)) atTop (fun _ => θ))
    {g : ℝ → ℝ} {g' : ℝ} (hg : HasStrictDerivAt g g' θ) :
    IsBootstrapLinear P O (fun n y => g (T n y)) (fun z => g' * ψ z) := by
  have hθ : ResampleTendstoZero P O fun n ω (_ : Fin n → 𝒪) => T n (dataPrefix O n ω) - θ :=
    ResampleTendstoZero.of_tendstoInMeasure hθ'
  have hR := hlin.resampleTendstoZero
  have hS := resampleBounded_sqrt_mul_resampleMean_sub_sampleMean hO hψ hψ2
  have hD : ResampleBounded P O fun n ω y => √(n : ℝ) * (T n y - T n (dataPrefix O n ω)) :=
    (hR.bounded.add hS).of_le (ResampleEventually.of_eventually
      (Eventually.of_forall fun n ω y => le_of_eq (by simp only [bootstrapRemainder]; ring_nf)))
  have hTd := hD.resampleTendstoZero_of_sqrt_mul
  have hTs := hTd.add hθ
  -- the strict derivative as an inequality near `θ`
  have hloc : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ a b : ℝ, |a - θ| < η → |b - θ| < η →
      |g a - g b - g' * (a - b)| ≤ ε * |a - b| := fun ε hε => by
    have h := hg.hasStrictFDerivAt.isLittleO.def hε
    obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 h
    refine ⟨η, hη, fun a b ha hb => ?_⟩
    have hd : dist (a, b) (θ, θ) < η := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt ha hb
    have := hball hd
    simpa only [Real.norm_eq_abs, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      mul_comm (a - b)] using this
  have hmain : ResampleTendstoZero P O fun n ω y => √(n : ℝ) *
      (g (T n y) - g (T n (dataPrefix O n ω)) - g' * (T n y - T n (dataPrefix O n ω))) := by
    refine ResampleTendstoZero.of_le_mul hD fun ε hε => ?_
    obtain ⟨η, hη, hgη⟩ := hloc ε hε
    refine ((hTs η hη).and (hθ η hη)).mono fun n ω y ⟨h1, h2⟩ => ?_
    simp only at h1 h2
    have h1' : |T n y - θ| < η := by
      have : T n y - T n (dataPrefix O n ω) + (T n (dataPrefix O n ω) - θ) = T n y - θ := by
        ring
      rwa [this] at h1
    have hsq := Real.sqrt_nonneg (n : ℝ)
    rw [abs_mul, abs_mul, abs_of_nonneg hsq]
    calc √(n : ℝ) * |g (T n y) - g (T n (dataPrefix O n ω)) -
          g' * (T n y - T n (dataPrefix O n ω))|
        ≤ √(n : ℝ) * (ε * |T n y - T n (dataPrefix O n ω)|) :=
          mul_le_mul_of_nonneg_left (hgη _ _ h1' h2) hsq
      _ = ε * (√(n : ℝ) * |T n y - T n (dataPrefix O n ω)|) := by ring
  refine isBootstrapLinear_of_resampleTendstoZero ((hmain.add (hR.const_mul g')).of_le
    (ResampleEventually.of_eventually (Eventually.of_forall fun n ω y => le_of_eq ?_)))
  congr 1
  simp only [bootstrapRemainder, resampleMean_const_mul, sampleMean_const_mul]
  ring

end General

/-! ### The weighted arm mean on the log and logit scales -/

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Bootstrap coverage on a smooth scale.** Under the hypotheses of the asymptotic normality
theorem of the weighted arm mean, a function `g` with strict derivative `g' ≠ 0` at `m₀`, and
`σ² > 0`, the bootstrap percentile and basic intervals of `g(m*)` cover `g(m₀)` with
probability tending to `1 - α`. -/
theorem tendsto_bootstrapArmMean_comp_coverage [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    {g : ℝ → ℝ} (hgm : Measurable g) {g' : ℝ}
    (hg : HasStrictDerivAt g g' (tiltArmMean (P.map (O 0)) φ t a
      (tiltMinimizer (P.map (O 0)) φ t))) (hg' : g' ≠ 0)
    (hσ : 0 < weightedArmVariance (P.map (O 0)) φ t a) {α z : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | g (tiltArmMean (P.map (O 0)) φ t a
        (tiltMinimizer (P.map (O 0)) φ t)) ∈
          percentileInterval (bootstrapLaw (fun n y => g (bootstrapArmMean φ t a n y)) O n ω)
            α}) atTop (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω | g (tiltArmMean (P.map (O 0)) φ t a
        (tiltMinimizer (P.map (O 0)) φ t)) ∈
          basicInterval (bootstrapLaw (fun n y => g (bootstrapArmMean φ t a n y)) O n ω)
            (g (sampleBalancedArmMean φ t O a n ω)) α}) atTop (𝓝 (1 - α)) := by
  have hAL := sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin a hq hy
  have hlin := isBootstrapLinear_bootstrapArmMean hO hφ hB hδ hmargin a hq hy
  have hψ2 : MemLp (weightedArmInfluence (P.map (O 0)) φ t a) 2 (P.map (O 0)) :=
    (memLp_map_measure_iff hAL.measurable.aestronglyMeasurable (hO.aemeasurable 0)).2
      hAL.memLp
  have hglin := hlin.comp_hasStrictDerivAt hO hAL.measurable hψ2
    (tendstoInMeasure_of_isAsymptoticallyLinear hO hAL) hg
  have hgAL := hAL.comp_hasDerivAt hO hg.hasDerivAt
  refine hglin.tendsto_coverage hO (fun n => hgm.comp (measurable_bootstrapArmMean hφ t a n))
    hgAL ?_ hα hz
  rw [integral_sq_comp_eq hO (hAL.measurable.const_mul g')]
  simp only [mul_pow]
  rw [integral_const_mul]
  exact mul_pos (pow_pos (abs_pos.2 hg') 2 |>.trans_eq (sq_abs g')) hσ

/-- **Bootstrap coverage on the log scale**: for `m₀ > 0` and `σ² > 0`, the bootstrap
intervals of `log m*` cover `log m₀` with probability tending to `1 - α`. -/
theorem tendsto_bootstrapArmMean_log_coverage [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    (hm : 0 < tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t))
    (hσ : 0 < weightedArmVariance (P.map (O 0)) φ t a) {α z : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | Real.log (tiltArmMean (P.map (O 0)) φ t a
        (tiltMinimizer (P.map (O 0)) φ t)) ∈ percentileInterval
          (bootstrapLaw (fun n y => Real.log (bootstrapArmMean φ t a n y)) O n ω) α}) atTop
        (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω | Real.log (tiltArmMean (P.map (O 0)) φ t a
        (tiltMinimizer (P.map (O 0)) φ t)) ∈ basicInterval
          (bootstrapLaw (fun n y => Real.log (bootstrapArmMean φ t a n y)) O n ω)
            (Real.log (sampleBalancedArmMean φ t O a n ω)) α}) atTop (𝓝 (1 - α)) :=
  tendsto_bootstrapArmMean_comp_coverage hO hφ hB hδ hmargin a hq hy Real.measurable_log
    (Real.hasStrictDerivAt_log hm.ne') (inv_ne_zero hm.ne') hσ hα hz

/-- The strict derivative of the logit `log (x / (1 - x))` at `m ∈ (0, 1)` is
`1 / (m (1 - m))`. -/
theorem hasStrictDerivAt_logit {m : ℝ} (hm0 : 0 < m) (hm1 : m < 1) :
    HasStrictDerivAt (fun x => Real.log (x / (1 - x))) (1 / (m * (1 - m))) m := by
  have h1 : (1 : ℝ) - m ≠ 0 := by linarith
  have hd := (hasStrictDerivAt_id m).div ((hasStrictDerivAt_const m (1 : ℝ)).sub
    (hasStrictDerivAt_id m)) h1
  have hl := hd.log (div_ne_zero hm0.ne' h1)
  refine hl.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.div_apply, id]
  field_simp
  ring

/-- **Bootstrap coverage on the logit scale**: for `0 < m₀ < 1` and `σ² > 0`, the bootstrap
intervals of `log (m* / (1 - m*))` cover `log (m₀ / (1 - m₀))` with probability tending to
`1 - α`. -/
theorem tendsto_bootstrapArmMean_logit_coverage [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    (hm0 : 0 < tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t))
    (hm1 : tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t) < 1)
    (hσ : 0 < weightedArmVariance (P.map (O 0)) φ t a) {α z : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω |
        (fun x => Real.log (x / (1 - x))) (tiltArmMean (P.map (O 0)) φ t a
          (tiltMinimizer (P.map (O 0)) φ t)) ∈ percentileInterval
          (bootstrapLaw (fun n y => (fun x => Real.log (x / (1 - x)))
            (bootstrapArmMean φ t a n y)) O n ω) α}) atTop (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω |
        (fun x => Real.log (x / (1 - x))) (tiltArmMean (P.map (O 0)) φ t a
          (tiltMinimizer (P.map (O 0)) φ t)) ∈ basicInterval
          (bootstrapLaw (fun n y => (fun x => Real.log (x / (1 - x)))
            (bootstrapArmMean φ t a n y)) O n ω)
            ((fun x => Real.log (x / (1 - x))) (sampleBalancedArmMean φ t O a n ω)) α}) atTop
        (𝓝 (1 - α)) :=
  tendsto_bootstrapArmMean_comp_coverage hO hφ hB hδ hmargin a hq hy
    (Real.measurable_log.comp (measurable_id.div (measurable_const.sub measurable_id)))
    (hasStrictDerivAt_logit hm0 hm1)
    (one_div_ne_zero (mul_ne_zero hm0.ne' (by linarith))) hσ hα hz

/-! ### The two coin model with one matched feature -/

section Example

variable {O : ℕ → Ω → Bool × Bool × ℝ} [IsProbabilityMeasure P]

/-- **The log scale in the treated arm**: the bootstrap intervals of `log m*` cover `log 2`
with probability tending to `1 - α`. -/
theorem example_bootstrap_log_coverage_true (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | Real.log 2 ∈ percentileInterval
        (bootstrapLaw (fun n y => Real.log (bootstrapArmMean exampleFeature exampleTarget true
          n y)) O n ω) α}) atTop (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω | Real.log 2 ∈ basicInterval
        (bootstrapLaw (fun n y => Real.log (bootstrapArmMean exampleFeature exampleTarget true
          n y)) O n ω)
          (Real.log (sampleBalancedArmMean exampleFeature exampleTarget O true n ω)) α}) atTop
        (𝓝 (1 - α)) := by
  have h := tendsto_bootstrapArmMean_log_coverage hO measurable_exampleFeature example_bound
    (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin) true
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)
    (by rw [hlaw, example_tiltArmMean_true]; norm_num)
    (by rw [hlaw, example_weightedArmVariance_true]; norm_num) hα hz
  rwa [hlaw, example_tiltArmMean_true] at h

/-- **The logit scale in the control arm**: the bootstrap intervals of `log (m* / (1 - m*))`
cover `log ((1/2) / (1 - 1/2)) = 0` with probability tending to `1 - α`. -/
theorem example_bootstrap_logit_coverage_false (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | (0 : ℝ) ∈ percentileInterval
        (bootstrapLaw (fun n y => (fun x => Real.log (x / (1 - x)))
          (bootstrapArmMean exampleFeature exampleTarget false n y)) O n ω) α}) atTop
        (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω | (0 : ℝ) ∈ basicInterval
        (bootstrapLaw (fun n y => (fun x => Real.log (x / (1 - x)))
          (bootstrapArmMean exampleFeature exampleTarget false n y)) O n ω)
          ((fun x => Real.log (x / (1 - x)))
            (sampleBalancedArmMean exampleFeature exampleTarget O false n ω)) α}) atTop
        (𝓝 (1 - α)) := by
  have h := tendsto_bootstrapArmMean_logit_coverage hO measurable_exampleFeature example_bound
    (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin) false
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)
    (by rw [hlaw, example_tiltArmMean_false]; norm_num)
    (by rw [hlaw, example_tiltArmMean_false]; norm_num)
    (by rw [hlaw, example_weightedArmVariance_false]; norm_num) hα hz
  have h0 : (fun x : ℝ => Real.log (x / (1 - x))) (1 / 2) = 0 := by norm_num
  rwa [hlaw, example_tiltArmMean_false, h0] at h

end Example

end PopulationAdjustment

end CausalInference
