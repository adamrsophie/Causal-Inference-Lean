/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.BootstrapQuantile
public import CausalInference.Estimation.PosteriorLimitCoverage

/-!
# Asymptotic coverage of bootstrap confidence intervals

Let `θ̂_n` estimate a real `θ` with `√n (θ̂_n - θ) → N(0, σ²)` in law, `σ² > 0`, and let `Q_n ω`
be the bootstrap law of `θ*_n` given the data, with `√n (θ*_n - θ̂_n)` given the data converging
weakly to `N(0, σ²)` in probability (the weak Bernstein and von Mises predicate
`PosteriorLimit.IsBernsteinVonMisesWeak P Q θ̂ N(0, σ²)`). With `q*_n(p)` the quantiles of `Q_n ω`
and `Φ(z) = 1 - α/2`, `α ∈ (0, 1)`:

* the **percentile interval** `[q*_n(α/2), q*_n(1 - α/2)]` covers `θ` with probability tending to
  `1 - α` (`Bootstrap.tendsto_percentileInterval_coverage`);
* the **basic interval** `[2 θ̂_n - q*_n(1 - α/2), 2 θ̂_n - q*_n(α/2)]` covers `θ` with probability
  tending to `1 - α` (`Bootstrap.tendsto_basicInterval_coverage`).

No measurability of the quantiles in the data is used. Both coverage events are squeezed between
events `{|√n (θ̂_n - θ)| ≤ σ z ± δ}`, up to the event that a rescaled quantile is more than `δ` from
its limit, whose outer probability tends to zero (`Bootstrap.tendsto_measureReal_squeeze`); the
probabilities are those of `P.real`, the outer measure on sets that need not be measurable.

**The degenerate case `σ² = 0`.** The hypothesis `σ² > 0` cannot be dropped: if the data are
almost surely constant, the bootstrap law of the mean is a point mass at `θ̂_n = θ`, both intervals
are `{θ}` and the coverage is `1` for every `n`, not `1 - α`
(`Bootstrap.percentileInterval_resampleMean_const`). The limit `N(0, 0)` has an atom at `0`,
where its distribution function does not cross the levels `α / 2` and `1 - α / 2` strictly.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 23.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace CausalInference

namespace Bootstrap

open PosteriorLimit BiasAnalysis.Distributions

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {P : Measure Ω}

/-- The percentile interval `[q(α/2), q(1 - α/2)]` of a law `Q` on `ℝ`. -/
noncomputable def percentileInterval (Q : Measure ℝ) (α : ℝ) : Set ℝ :=
  Icc (quantile Q (α / 2)) (quantile Q (1 - α / 2))

/-- The basic interval `[2a - q(1 - α/2), 2a - q(α/2)]` of a law `Q` on `ℝ` around the estimate
`a`: the percentile interval reflected about `a`. -/
noncomputable def basicInterval (Q : Measure ℝ) (a α : ℝ) : Set ℝ :=
  Icc (2 * a - quantile Q (1 - α / 2)) (2 * a - quantile Q (α / 2))

/-- The critical value `z` with `Φ(z) = 1 - α/2`, `α ∈ (0, 1)`, is positive. -/
theorem pos_of_cdf_eq {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) : 0 < z := by
  have hzn : cdf (gaussianReal 0 1) (-z) = α / 2 := by
    rw [cdf_gaussianReal_zero_one_neg, hz]; ring
  have hlt : cdf (gaussianReal 0 1) (-z) < cdf (gaussianReal 0 1) z := by
    rw [hzn, hz]; linarith [hα.2]
  have := (cdf_gaussianReal_strictMono 0 (v := 1) one_ne_zero).lt_iff_lt.1 hlt
  linarith

/-- For `σ = √v`, `v > 0`, and `Φ(z) = 1 - α/2`, `N(0, v)` gives `[-σ z, σ z]` mass `1 - α`. -/
theorem cdf_sub_cdf_neg_eq {v : ℝ} (hv : 0 < v) {α z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    cdf (gaussianReal 0 v.toNNReal) (√v * z) - cdf (gaussianReal 0 v.toNNReal) (-(√v * z)) =
      1 - α := by
  have hs : 0 < √v := Real.sqrt_pos.2 hv
  have hvv : ((v.toNNReal : ℝ≥0) : ℝ) = √v ^ 2 := by
    rw [Real.coe_toNNReal _ hv.le, Real.sq_sqrt hv.le]
  have h1 : cdf (gaussianReal 0 v.toNNReal) (√v * z) = 1 - α / 2 := by
    rw [show √v * z = 0 + √v * z by ring, cdf_gaussianReal_affine 0 hs hvv z, hz]
  have h2 : cdf (gaussianReal 0 v.toNNReal) (-(√v * z)) = α / 2 := by
    rw [show -(√v * z) = 0 + √v * (-z) by ring, cdf_gaussianReal_affine 0 hs hvv (-z),
      cdf_gaussianReal_zero_one_neg, hz]
    ring
  rw [h1, h2]
  ring

/-- **The squeeze.** Let `T_n → N(0, v)` in law with `v > 0` under a probability measure `P`, let
`L_n → -c` and `U_n → c` in probability with `c > 0`, and let `R_n` satisfy `|R_n| = |T_n|`. If,
eventually, the event `C_n` is `{L_n ≤ R_n ≤ U_n}`, then `P(C_n) → F(c) - F(-c)`, with `F` the
distribution function of `N(0, v)`. Neither `L_n`, `U_n` nor `C_n` needs to be measurable:
`P(C_n)` is the outer probability. -/
theorem tendsto_measureReal_squeeze [IsProbabilityMeasure P] {T R Lq Uq : ℕ → Ω → ℝ}
    {Cv : ℕ → Set Ω} {v : ℝ} (hv : 0 < v) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 v.toNNReal) P')
    (hT : TendstoInDistribution T atTop Y (fun _ ↦ P) P') {c : ℝ} (hc : 0 < c)
    (hlo : TendstoInMeasure P Lq atTop (fun _ ↦ -c))
    (hhi : TendstoInMeasure P Uq atTop (fun _ ↦ c)) (hR : ∀ n ω, |R n ω| = |T n ω|)
    (hmem : ∀ᶠ n in atTop, ∀ ω, ω ∈ Cv n ↔ Lq n ω ≤ R n ω ∧ R n ω ≤ Uq n ω) :
    Tendsto (fun n ↦ P.real (Cv n)) atTop
      (𝓝 (cdf (gaussianReal 0 v.toNNReal) c - cdf (gaussianReal 0 v.toNNReal) (-c))) := by
  have hv0 : v.toNNReal ≠ 0 := by simpa using hv
  set F := cdf (gaussianReal 0 v.toNNReal) with hF
  set G : ℝ → ℝ := fun c ↦ F c - F (-c) with hG
  have hFc : Continuous F := continuous_cdf_gaussianReal hv0
  have hGc : Continuous G := hFc.sub (hFc.comp continuous_neg)
  have hlawY : P'.map Y = gaussianReal 0 v.toNNReal := hY.map_eq
  have hTlim : ∀ c, 0 ≤ c → Tendsto (fun n ↦ P.real {ω | |T n ω| ≤ c}) atTop (𝓝 (G c)) := by
    intro c hc
    have : NullSingletonClass (gaussianReal 0 v.toNNReal) := nullSingletonClass_gaussianReal hv0
    have hnull : P'.map Y (frontier (Icc (-c) c)) = 0 := by
      rw [hlawY, frontier_Icc (by linarith)]
      exact (Set.toFinite _).measure_zero _
    have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hT.tendsto
      (E := Icc (-c) c) hnull
    simp only [ProbabilityMeasure.coe_mk] at hport
    have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
    have hval : (P'.map Y (Icc (-c) c)).toReal = G c := by
      rw [hlawY, ← measureReal_def]
      have hIcc : Icc (-c) c = Iic c \ Iio (-c) := by ext x; simp [and_comm]
      rw [hIcc, measureReal_sdiff (fun x hx ↦ by simp only [mem_Iio] at hx; simp; linarith)
        measurableSet_Iio, measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real, ← cdf_eq_real]
    rw [hval] at hreal
    refine hreal.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    rw [Measure.map_apply_of_aemeasurable (hT.forall_aemeasurable n) measurableSet_Icc,
      measureReal_def]
    congr 2
    ext ω
    simp only [mem_preimage, mem_Icc, Set.mem_ofPred_eq, abs_le]
  set Gd : ℝ → ℕ → Set Ω := fun δ n ↦
    {ω | dist (Lq n ω) (-c) < δ} ∩ {ω | dist (Uq n ω) c < δ} with hGd
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hmem
  have hsub1 : ∀ δ, ∀ n, N₀ ≤ n → Cv n ⊆ {ω | |T n ω| ≤ c + δ} ∪ (Gd δ n)ᶜ := by
    intro δ n hn ω hω
    by_cases hg : ω ∈ Gd δ n
    · left
      obtain ⟨h1, h2⟩ := (hN₀ n hn ω).1 hω
      obtain ⟨g1, g2⟩ := hg
      simp only [Set.mem_ofPred_eq, Real.dist_eq, abs_lt] at g1 g2 ⊢
      rw [← hR, abs_le]
      constructor <;> linarith [g1.1, g1.2, g2.1, g2.2]
    · exact Or.inr hg
  have hsub2 : ∀ δ, ∀ n, N₀ ≤ n → {ω | |T n ω| ≤ c - δ} ⊆ Cv n ∪ (Gd δ n)ᶜ := by
    intro δ n hn ω hω
    by_cases hg : ω ∈ Gd δ n
    · left
      refine (hN₀ n hn ω).2 ?_
      obtain ⟨g1, g2⟩ := hg
      simp only [Set.mem_ofPred_eq, Real.dist_eq, abs_lt] at g1 g2 hω
      rw [← hR, abs_le] at hω
      constructor <;> linarith [g1.1, g1.2, g2.1, g2.2, hω.1, hω.2]
    · exact Or.inr hg
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨δ₀, hδ₀, hGδ⟩ := Metric.continuousAt_iff.1 hGc.continuousAt (ε / 4) hε4
  set δ := min (δ₀ / 2) (c / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ2 : δ ≤ c / 2 := min_le_right _ _
  have hGp : |G (c + δ) - G c| < ε / 4 := by
    rw [← Real.dist_eq]
    exact hGδ (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ0]; exact hδ1)
  have hGm : |G (c - δ) - G c| < ε / 4 := by
    rw [← Real.dist_eq]
    exact hGδ (by rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hδ0]; exact hδ1)
  have hgood := (hlo.withProbTendingToOne_dist_lt hδ0).inter (hhi.withProbTendingToOne_dist_lt hδ0)
  have hbad : Tendsto (fun n ↦ P.real (Gd δ n)ᶜ) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hgood
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (hTlim (c + δ) (by linarith)) (ε / 4) hε4
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (hTlim (c - δ) (by linarith)) (ε / 4) hε4
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.1 hbad (ε / 4) hε4
  refine ⟨max N₀ (max N₁ (max N₂ N₃)), fun n hn ↦ ?_⟩
  have hn1 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N₂ ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hn
  have hn4 : N₃ ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hn
  have e1 := hN₁ n hn2
  have e2 := hN₂ n hn3
  have e3 := hN₃ n hn4
  rw [Real.dist_eq] at e1 e2 e3
  rw [sub_zero, abs_of_nonneg measureReal_nonneg] at e3
  have u1 : P.real (Cv n) ≤ P.real {ω | |T n ω| ≤ c + δ} + P.real (Gd δ n)ᶜ :=
    (measureReal_mono (hsub1 δ n hn1)).trans (measureReal_union_le _ _)
  have u2 : P.real {ω | |T n ω| ≤ c - δ} ≤ P.real (Cv n) + P.real (Gd δ n)ᶜ :=
    (measureReal_mono (hsub2 δ n hn1)).trans (measureReal_union_le _ _)
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at e1 e2 hGp hGm
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hGp.1, hGp.2, hGm.1, hGm.2]

/-- **Asymptotic coverage of the percentile interval.** Let `√n (θ̂_n - θ) → N(0, σ²)` in law,
`σ² > 0`, and let the laws `Q_n ω` (the bootstrap laws of `θ*_n` given the data) satisfy the weak
Bernstein and von Mises predicate with centering `θ̂_n` and limit `N(0, σ²)`: `√n (θ*_n - θ̂_n)`
given the data converges weakly to `N(0, σ²)` in probability. For `α ∈ (0, 1)` and
`Φ(z) = 1 - α/2`, the probability that `[q*_n(α/2), q*_n(1 - α/2)]` contains `θ` tends to
`1 - α`. -/
theorem tendsto_percentileInterval_coverage [IsProbabilityMeasure P] {Q : ℕ → Ω → Measure ℝ}
    {θh : ℕ → Ω → ℝ} {σ2 : ℝ} (hσ : 0 < σ2)
    (hB : IsBernsteinVonMisesWeak P Q θh (gaussianReal 0 σ2.toNNReal)) {θ : ℝ}
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 σ2.toNNReal) P')
    (hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (θh n ω - θ)) atTop Y
      (fun _ ↦ P) P')
    {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | θ ∈ percentileInterval (Q n ω) α}) atTop (𝓝 (1 - α)) := by
  obtain ⟨hhi, hlo⟩ := hB.tendstoInMeasure_credibleInterval_endpoints hσ hz
  have hc : 0 < √σ2 * z := mul_pos (Real.sqrt_pos.2 hσ) (pos_of_cdf_eq hα hz)
  rw [← cdf_sub_cdf_neg_eq hσ hz]
  refine tendsto_measureReal_squeeze hσ hY hT hc hlo hhi (R := fun n ω ↦ -(√(n : ℝ) *
    (θh n ω - θ))) (fun n ω ↦ abs_neg _) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn ω
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  simp only [percentileInterval, mem_Icc]
  rw [show -(√(n : ℝ) * (θh n ω - θ)) = √(n : ℝ) * (θ - θh n ω) by ring,
    mul_le_mul_iff_right₀ hsq, mul_le_mul_iff_right₀ hsq]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Asymptotic coverage of the basic interval.** Under the hypotheses of
`Bootstrap.tendsto_percentileInterval_coverage`, the probability that
`[2 θ̂_n - q*_n(1 - α/2), 2 θ̂_n - q*_n(α/2)]` contains `θ` tends to `1 - α`. The basic interval
contains `θ` exactly when `√n (q*_n(α/2) - θ̂_n) ≤ √n (θ̂_n - θ) ≤ √n (q*_n(1 - α/2) - θ̂_n)`,
the percentile event with the sign of `√n (θ̂_n - θ)` reversed; the limit law is symmetric. -/
theorem tendsto_basicInterval_coverage [IsProbabilityMeasure P] {Q : ℕ → Ω → Measure ℝ}
    {θh : ℕ → Ω → ℝ} {σ2 : ℝ} (hσ : 0 < σ2)
    (hB : IsBernsteinVonMisesWeak P Q θh (gaussianReal 0 σ2.toNNReal)) {θ : ℝ}
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 σ2.toNNReal) P')
    (hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (θh n ω - θ)) atTop Y
      (fun _ ↦ P) P')
    {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | θ ∈ basicInterval (Q n ω) (θh n ω) α}) atTop
      (𝓝 (1 - α)) := by
  obtain ⟨hhi, hlo⟩ := hB.tendstoInMeasure_credibleInterval_endpoints hσ hz
  have hc : 0 < √σ2 * z := mul_pos (Real.sqrt_pos.2 hσ) (pos_of_cdf_eq hα hz)
  rw [← cdf_sub_cdf_neg_eq hσ hz]
  refine tendsto_measureReal_squeeze hσ hY hT hc hlo hhi (R := fun n ω ↦ √(n : ℝ) *
    (θh n ω - θ)) (fun n ω ↦ rfl) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn ω
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  simp only [basicInterval, mem_Icc]
  rw [mul_le_mul_iff_right₀ hsq, mul_le_mul_iff_right₀ hsq]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### The bootstrap of the mean -/

/-- **Coverage of the bootstrap intervals for the mean.** For an i.i.d. sample, `f` measurable
with `E[f(O_0)²] < ∞` and positive variance, `α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, both the
percentile interval and the basic interval of the bootstrap law of the resample mean cover
`E f(O_0)` with probability tending to `1 - α`. Every hypothesis of the general theorems is
discharged: the sampling limit is the central limit theorem, the bootstrap limit is
`Bootstrap.isBernsteinVonMisesWeak_resampleMean`. -/
theorem tendsto_bootstrap_coverage_resampleMean [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O P) {f : 𝒪 → ℝ} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 P)
    (hσ : 0 < Var[fun ω ↦ f (O 0 ω); P]) {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | P[fun ω ↦ f (O 0 ω)] ∈
        percentileInterval (bootstrapLaw (resampleMean f) O n ω) α}) atTop (𝓝 (1 - α)) ∧
      Tendsto (fun n ↦ P.real {ω | P[fun ω ↦ f (O 0 ω)] ∈
        basicInterval (bootstrapLaw (resampleMean f) O n ω) (sampleMean f O n ω) α}) atTop
        (𝓝 (1 - α)) := by
  have hB := isBernsteinVonMisesWeak_resampleMean hO hf hf2
  set N := gaussianReal 0 (Var[fun ω ↦ f (O 0 ω); P]).toNNReal
  have hY : HasLaw (fun x : ℝ ↦ x) N N := ⟨aemeasurable_id, Measure.map_id⟩
  have hX := hO.comp hf
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun i ω ↦ f (O i ω)) hY hf2
    hX.indep hX.ident
  have hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
      (sampleMean f O n ω - P[fun ω ↦ f (O 0 ω)])) atTop (fun x ↦ x) (fun _ ↦ P) N := by
    convert hclt using 2 with n
    funext ω
    rw [sampleMean]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hnr : (n : ℝ) = √(n : ℝ) * √(n : ℝ) := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    set r := √(n : ℝ)
    rw [hnr]
    field_simp
  exact ⟨tendsto_percentileInterval_coverage hσ hB hY hT hα hz,
    tendsto_basicInterval_coverage hσ hB hY hT hα hz⟩

end Bootstrap

end CausalInference
