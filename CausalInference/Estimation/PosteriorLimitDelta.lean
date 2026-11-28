/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitTotalVariation

/-!
# The posterior delta method

Let `Π_n(ω)` be random posterior laws on a normed space `E` that satisfy the Bernstein and von
Mises conclusion in its weak form with centering `θ̂_n` and limit `N`
(`IsBernsteinVonMisesWeak`), and let `θ̂_n → θ₀` in probability. For a functional `Ψ : E → ℝ`
strictly differentiable at `θ₀` with derivative `D`, the posterior law of the target `Ψ(θ)`,
centered at `Ψ(θ̂_n)` and scaled by `√n`, converges weakly in probability to the image law
`D_# N` (`IsBernsteinVonMisesWeak.map`). For `N = N(0, Σ)` and `D = ⟪d, ·⟫` the limit is
`N(0, dᵀ Σ d)`.

The proof: a continuous cutoff of the norm makes the rescaled posterior tight; on the ball where
the cutoff vanishes, the strict derivative bound gives
`|√n (Ψ(θ) - Ψ(θ̂_n)) - D(√n (θ - θ̂_n))|` small once `θ̂_n` is near `θ₀`, and uniform continuity
of the test function on a compact interval moves the test function across.

The total variation form transfers to the target in its own way: the posterior of `Ψ` stays
within `‖Π_n - N(θ̂_n, n⁻¹ ·)‖` of the image of the normal approximation under `Ψ`
(`IsBernsteinVonMises.tendstoInMeasure_tvDist_map`), so posterior probabilities of sets of target
values, data dependent sets included, are those of the normal approximation up to `o_p(1)`
(`IsBernsteinVonMises.tendstoInMeasure_measureReal_preimage_sub`).

## Main results

* `IsBernsteinVonMisesWeak.map`, `IsBernsteinVonMises.map`: the posterior delta method.
* `IsBernsteinVonMises.tendstoInMeasure_tvDist_map`,
  `IsBernsteinVonMises.tendstoInMeasure_measureReal_preimage_sub`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Events containing, for all large `n`, events of probability tending to one have probability
tending to one. -/
lemma withProbTendingToOne_of_eventually_subset {A B : ℕ → Set Ω}
    (hA : WithProbTendingToOne P A) (h : ∀ᶠ n in atTop, A n ⊆ B n) :
    WithProbTendingToOne P B :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hA
    (Eventually.of_forall fun _ ↦ zero_le)
    (h.mono fun _ hn ↦ measure_mono (Set.compl_subset_compl.2 hn))

/-- The continuous cutoff `min 1 (max 0 (‖z‖ - m))`: zero on `‖z‖ ≤ m`, one on `‖z‖ ≥ m + 1`. -/
noncomputable def normCutoff {E : Type*} [Norm E] (m : ℝ) (z : E) : ℝ := min 1 (max 0 (‖z‖ - m))

lemma continuous_normCutoff {E : Type*} [NormedAddCommGroup E] (m : ℝ) :
    Continuous (normCutoff (E := E) m) := by
  unfold normCutoff
  fun_prop

lemma normCutoff_mem_Icc {E : Type*} [NormedAddCommGroup E] (m : ℝ) (z : E) :
    0 ≤ normCutoff m z ∧ normCutoff m z ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- **The posterior delta method.** If the posteriors `Π_n` satisfy the weak Bernstein and von
Mises conclusion with centering `θ̂_n` and limit `N`, `θ̂_n → θ₀` in probability, and `Ψ` is
measurable and strictly differentiable at `θ₀` with derivative `D` (true for a continuously
differentiable `Ψ`), then the posterior laws `Ψ_# Π_n` of the target satisfy the weak Bernstein
and von Mises conclusion with centering `Ψ(θ̂_n)` and limit `D_# N`: for every bounded continuous
`φ`, `∫ φ(√n (Ψ(θ) - Ψ(θ̂_n))) dΠ_n(θ) → ∫ φ(D z) dN(z)` in probability. -/
theorem IsBernsteinVonMisesWeak.map [OpensMeasurableSpace E] {Pn : ℕ → Ω → Measure E}
    {θh : ℕ → Ω → E} {N : Measure E}
    (h : IsBernsteinVonMisesWeak P Pn θh N) {θ₀ : E}
    (hcons : TendstoInMeasure P θh atTop (fun _ ↦ θ₀)) {Ψ : E → ℝ} (hΨm : Measurable Ψ)
    {D : E →L[ℝ] ℝ} (hΨ : HasStrictFDerivAt Ψ D θ₀) :
    IsBernsteinVonMisesWeak P (fun n ω ↦ (Pn n ω).map Ψ) (fun n ω ↦ Ψ (θh n ω)) (N.map D) := by
  have := h.isProbabilityMeasure
  have := h.isProbabilityMeasure_limit
  refine ⟨fun n ω ↦ (Measure.isProbabilityMeasure_map_iff hΨm.aemeasurable).2 inferInstance,
    (Measure.isProbabilityMeasure_map_iff D.continuous.aemeasurable).2 inferInstance,
    fun φ hφ hφb ↦ ?_⟩
  -- move the integrals back to the parameter space
  have hpost : ∀ n ω, ∫ y, φ (√(n : ℝ) • (y - Ψ (θh n ω))) ∂(Pn n ω).map Ψ =
      ∫ θ, φ (√(n : ℝ) * (Ψ θ - Ψ (θh n ω))) ∂Pn n ω := fun n ω ↦ by
    rw [integral_map hΨm.aemeasurable (by fun_prop : Continuous fun y : ℝ ↦
      φ (√(n : ℝ) • (y - Ψ (θh n ω)))).aestronglyMeasurable]
    simp only [smul_eq_mul]
  have hlimD : ∫ y, φ y ∂N.map D = ∫ z, φ (D z) ∂N :=
    integral_map D.continuous.aemeasurable hφ.aestronglyMeasurable
  simp only [hpost, hlimD]
  obtain ⟨C, hC⟩ := hφb
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hB := h.tendsto (fun z ↦ φ (D z)) (hφ.comp D.continuous) ⟨C, fun z ↦ hC _⟩
  refine TendstoInMeasure.of_perturb hB (tendstoInMeasure_const (1 : ℝ)) fun ε hε ↦ ?_
  simp only [mul_one]
  -- the cutoff level
  set η := ε / (16 * (C + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hdom : Tendsto (fun m : ℕ ↦ ∫ z, normCutoff (m : ℝ) z ∂N) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := N) (fun _ ↦ (1 : ℝ))
      (F := fun (m : ℕ) (z : E) ↦ normCutoff (m : ℝ) z) (f := fun _ ↦ 0)
      (fun m ↦ (continuous_normCutoff _).aestronglyMeasurable) (integrable_const 1)
      (fun m ↦ ae_of_all _ fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (normCutoff_mem_Icc _ z).1]
        exact (normCutoff_mem_Icc _ z).2)
      (ae_of_all _ fun z ↦ by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈‖z‖⌉₊] with m hm
        have : ‖z‖ ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm)
        simp only [normCutoff]
        rw [max_eq_left (by linarith), min_eq_right zero_le_one])
    simpa using this
  obtain ⟨m, hm⟩ := (hdom.eventually (gt_mem_nhds hη0)).exists
  set K : ℝ := m + 1 with hK
  have hK0 : 0 < K := by positivity
  -- uniform continuity of `φ` on a compact interval
  set R := ‖D‖ * K + 1 with hR
  obtain ⟨ρ, hρ, hφu⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := -R) (b := R)).uniformContinuousOn_of_continuous hφ.continuousOn)
    (ε / 2) (by positivity)
  set ρ' := min ρ 1 with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ zero_lt_one
  -- strict differentiability
  obtain ⟨δ, hδ, hloc⟩ := Metric.eventually_nhds_iff.1
    ((hasStrictFDerivAt_iff_isLittleO.1 hΨ).def (c := ρ' / (2 * K)) (by positivity))
  -- the good events
  have hG := ((h.tendsto _ (continuous_normCutoff m) ⟨1, fun z ↦ by
      rw [abs_of_nonneg (normCutoff_mem_Icc _ z).1]; exact (normCutoff_mem_Icc _ z).2⟩
      ).withProbTendingToOne_dist_lt hη0).inter
    (hcons.withProbTendingToOne_dist_lt (half_pos hδ))
  refine withProbTendingToOne_of_eventually_subset hG ?_
  have htend : Tendsto (fun n : ℕ ↦ K / √(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [htend.eventually (gt_mem_nhds (half_pos hδ)), eventually_gt_atTop 0]
    with n hnK hn
  rintro ω ⟨hω1, hω2⟩
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω1 hω2 ⊢
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  set c := θh n ω with hc
  -- pointwise bound on the integrand
  have hpt : ∀ θ, |φ (√(n : ℝ) * (Ψ θ - Ψ c)) - φ (D (√(n : ℝ) • (θ - c)))| ≤
      ε / 2 + 2 * C * normCutoff m (√(n : ℝ) • (θ - c)) := by
    intro θ
    set z := √(n : ℝ) • (θ - c) with hz
    by_cases hzK : K ≤ ‖z‖
    · have : normCutoff m z = 1 := by
        simp only [normCutoff]
        rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      rw [this]
      have := abs_sub (φ (√(n : ℝ) * (Ψ θ - Ψ c))) (φ (D z))
      linarith [hC (√(n : ℝ) * (Ψ θ - Ψ c)), hC (D z), abs_nonneg (φ (D z))]
    push Not at hzK
    have hnz : ‖z‖ = √(n : ℝ) * ‖θ - c‖ := by
      rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos hsq]
    have hθc : ‖θ - c‖ < δ / 2 := by
      have : ‖θ - c‖ < K / √(n : ℝ) := by
        rw [lt_div_iff₀ hsq, mul_comm, ← hnz]
        exact hzK
      linarith
    have hc0 : dist c θ₀ < δ / 2 := hω2
    have hmem : dist (θ, c) (θ₀, θ₀) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      constructor
      · calc dist θ θ₀ ≤ dist θ c + dist c θ₀ := dist_triangle _ _ _
          _ < δ / 2 + δ / 2 := by rw [dist_eq_norm]; exact add_lt_add hθc hc0
          _ = δ := add_halves δ
      · linarith
    have hdiff := hloc hmem
    simp only [Real.norm_eq_abs] at hdiff
    have hDz : D z = √(n : ℝ) * D (θ - c) := by
      rw [hz, D.map_smul, smul_eq_mul]
    have hr : |√(n : ℝ) * (Ψ θ - Ψ c) - D z| < ρ' := by
      rw [hDz, ← mul_sub, abs_mul, abs_of_pos hsq]
      calc √(n : ℝ) * |Ψ θ - Ψ c - D (θ - c)| ≤ √(n : ℝ) * (ρ' / (2 * K) * ‖θ - c‖) :=
            mul_le_mul_of_nonneg_left hdiff hsq.le
        _ = ρ' / (2 * K) * ‖z‖ := by rw [hnz]; ring
        _ ≤ ρ' / (2 * K) * K := mul_le_mul_of_nonneg_left hzK.le (by positivity)
        _ < ρ' := by field_simp; linarith
    have hDzR : |D z| ≤ ‖D‖ * K := by
      rw [← Real.norm_eq_abs]
      exact (D.le_opNorm z).trans (mul_le_mul_of_nonneg_left hzK.le (norm_nonneg _))
    have h1 : D z ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc, ← abs_le]; linarith
    have h2 : √(n : ℝ) * (Ψ θ - Ψ c) ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc, ← abs_le]
      have := abs_sub_abs_le_abs_sub (√(n : ℝ) * (Ψ θ - Ψ c)) (D z)
      linarith [min_le_right ρ 1]
    have hdist : dist (√(n : ℝ) * (Ψ θ - Ψ c)) (D z) < ρ := by
      rw [Real.dist_eq]; linarith [min_le_left ρ 1]
    have := hφu _ h2 _ h1 hdist
    rw [Real.dist_eq] at this
    nlinarith [(normCutoff_mem_Icc m z).1]
  -- integrate the bound
  have hfm : Measurable fun θ ↦ φ (√(n : ℝ) * (Ψ θ - Ψ c)) :=
    hφ.measurable.comp ((hΨm.sub_const _).const_mul _)
  have hgc : Continuous fun θ : E ↦ φ (D (√(n : ℝ) • (θ - c))) := by fun_prop
  have hχm : Continuous fun θ : E ↦ normCutoff m (√(n : ℝ) • (θ - c)) :=
    (continuous_normCutoff m).comp (by fun_prop)
  have hfi : Integrable (fun θ ↦ φ (√(n : ℝ) * (Ψ θ - Ψ c))) (Pn n ω) :=
    Integrable.of_bound hfm.aestronglyMeasurable C (ae_of_all _ fun θ ↦ hC _)
  have hgi : Integrable (fun θ ↦ φ (D (√(n : ℝ) • (θ - c)))) (Pn n ω) :=
    Integrable.of_bound hgc.aestronglyMeasurable C (ae_of_all _ fun θ ↦ hC _)
  have hχi : Integrable (fun θ ↦ normCutoff m (√(n : ℝ) • (θ - c))) (Pn n ω) :=
    Integrable.of_bound hχm.aestronglyMeasurable 1 (ae_of_all _ fun θ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (normCutoff_mem_Icc _ _).1]
      exact (normCutoff_mem_Icc _ _).2)
  have hχN : ∫ z, normCutoff (m : ℝ) z ∂N < η := hm
  have hχP : ∫ θ, normCutoff m (√(n : ℝ) • (θ - c)) ∂Pn n ω < 2 * η := by
    have := (abs_lt.1 hω1).2
    linarith
  rw [← integral_sub hfi hgi]
  calc |∫ θ, φ (√(n : ℝ) * (Ψ θ - Ψ c)) - φ (D (√(n : ℝ) • (θ - c))) ∂Pn n ω|
      ≤ ∫ θ, |φ (√(n : ℝ) * (Ψ θ - Ψ c)) - φ (D (√(n : ℝ) • (θ - c)))| ∂Pn n ω :=
        abs_integral_le_integral_abs
    _ ≤ ∫ θ, (ε / 2 + 2 * C * normCutoff m (√(n : ℝ) • (θ - c))) ∂Pn n ω :=
        integral_mono (hfi.sub hgi).abs ((integrable_const _).add (hχi.const_mul _)) hpt
    _ = ε / 2 + 2 * C * ∫ θ, normCutoff m (√(n : ℝ) • (θ - c)) ∂Pn n ω := by
        rw [integral_add (integrable_const _) (hχi.const_mul _), integral_const_mul,
          integral_const, probReal_univ, one_smul]
    _ ≤ ε := by
        have : 2 * C * ∫ θ, normCutoff m (√(n : ℝ) • (θ - c)) ∂Pn n ω ≤ 2 * C * (2 * η) :=
          mul_le_mul_of_nonneg_left hχP.le (by positivity)
        have h4 : 2 * C * (2 * η) ≤ ε / 4 := by
          rw [hη]
          field_simp
          nlinarith
        linarith

variable [BorelSpace E]

/-- **The posterior delta method from the total variation form**: `IsBernsteinVonMisesWeak.map`
under the total variation form of the Bernstein and von Mises conclusion. -/
theorem IsBernsteinVonMises.map {Pn : ℕ → Ω → Measure E} {θh : ℕ → Ω → E} {N : Measure E}
    (h : IsBernsteinVonMises P Pn θh N) {θ₀ : E}
    (hcons : TendstoInMeasure P θh atTop (fun _ ↦ θ₀)) {Ψ : E → ℝ} (hΨm : Measurable Ψ)
    {D : E →L[ℝ] ℝ} (hΨ : HasStrictFDerivAt Ψ D θ₀) :
    IsBernsteinVonMisesWeak P (fun n ω ↦ (Pn n ω).map Ψ) (fun n ω ↦ Ψ (θh n ω)) (N.map D) :=
  h.isBernsteinVonMisesWeak.map hcons hΨm hΨ

/-- **The posterior of the target and the image of the normal approximation.** Under the total
variation form, `‖Ψ_# Π_n - Ψ_# N(θ̂_n, n⁻¹ ·)‖ → 0` in probability for every measurable `Ψ`;
no differentiability is needed. -/
theorem IsBernsteinVonMises.tendstoInMeasure_tvDist_map {Pn : ℕ → Ω → Measure E}
    {θh : ℕ → Ω → E} {N : Measure E} (h : IsBernsteinVonMises P Pn θh N) {F : Type*}
    [MeasurableSpace F] {Ψ : E → F} (hΨm : Measurable Ψ) :
    TendstoInMeasure P (fun n ω ↦ tvDist ((Pn n ω).map Ψ)
      ((N.map fun z ↦ θh n ω + (√(n : ℝ))⁻¹ • z).map Ψ)) atTop (fun _ ↦ 0) := by
  have := h.isProbabilityMeasure
  have := h.isProbabilityMeasure_limit
  have htv := h.tendsto
  rw [tendstoInMeasure_iff_dist] at htv ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (htv ε hε)
    (fun _ ↦ zero_le) fun n ↦ measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  have : IsProbabilityMeasure (N.map fun z ↦ θh n ω + (√(n : ℝ))⁻¹ • z) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
  rw [abs_of_nonneg tvDist_nonneg] at hω ⊢
  exact hω.trans (tvDist_map_le hΨm)

/-- **Posterior probabilities of target sets.** Under the total variation form, for measurable
sets `I n ω` of target values that may depend on the data (a credible interval, for example),
`Π_n(Ψ ∈ I_n) - N(θ̂_n, n⁻¹ ·)(Ψ ∈ I_n) → 0` in probability. -/
theorem IsBernsteinVonMises.tendstoInMeasure_measureReal_preimage_sub
    {Pn : ℕ → Ω → Measure E} {θh : ℕ → Ω → E} {N : Measure E}
    (h : IsBernsteinVonMises P Pn θh N) {Ψ : E → ℝ} (hΨm : Measurable Ψ)
    {I : ℕ → Ω → Set ℝ} (hI : ∀ n ω, MeasurableSet (I n ω)) :
    TendstoInMeasure P (fun n ω ↦ (Pn n ω).real (Ψ ⁻¹' I n ω) -
      (N.map fun z ↦ θh n ω + (√(n : ℝ))⁻¹ • z).real (Ψ ⁻¹' I n ω)) atTop (fun _ ↦ 0) := by
  have := h.isProbabilityMeasure
  have := h.isProbabilityMeasure_limit
  have htv := h.tendsto
  rw [tendstoInMeasure_iff_dist] at htv ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (htv ε hε)
    (fun _ ↦ zero_le) fun n ↦ measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  have : IsProbabilityMeasure (N.map fun z ↦ θh n ω + (√(n : ℝ))⁻¹ • z) :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
  rw [abs_of_nonneg tvDist_nonneg]
  exact hω.trans (abs_measureReal_sub_le_tvDist (hΨm (hI n ω)))

end PosteriorLimit

end CausalInference
