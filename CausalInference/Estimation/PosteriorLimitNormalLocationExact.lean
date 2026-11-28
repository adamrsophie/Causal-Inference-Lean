/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitNormalLocation
public import CausalInference.MetaAnalysis.CochranQLaw

/-!
# Exact finite sample coverage in the normal location model

The observations `Y₀, Y₁, ...` are i.i.d. with law `N(θ₀, σ²)`, `σ² > 0`, and `n ≥ 1`. Let `Φ` be
the standard normal distribution function and `Φ(z) = 1 - α/2` with `α ≤ 1` (so `z ≥ 0`).

* `hasLaw_sampleMean_gaussianReal`: the sample mean `Ȳ_n` has the law `N(θ₀, σ²/n)`, the case
  of equal variances of the law of the inverse variance weighted estimate.
* `measureReal_mem_waldInterval_sampleMean`: the Wald interval `Ȳ_n ∓ z σ/√n` covers `θ₀` with
  probability exactly `1 - α`. Hence the equal tailed credible interval of `N(Ȳ_n, σ²/n)`, the
  flat prior limit of the posterior, has exact coverage `1 - α`
  (`measureReal_mem_credibleInterval_flat`).
* `hasLaw_posteriorMean_sub_gaussianReal`: under the proper normal prior `N(m₀, τ²)` the
  posterior is `N(m_n, v_n)` with `v_n = 1/(1/τ² + n/σ²)`, and `m_n - θ₀ ~ N(b_n, s_n²)` with
  `b_n = v_n (m₀ - θ₀)/τ²` and `s_n = v_n √n/σ`.
* `measureReal_mem_credibleInterval_normalLocation`: the coverage of the equal tailed credible
  interval is exactly `Φ((z√v_n - b_n)/s_n) - Φ((-z√v_n - b_n)/s_n)`.
* `measureReal_mem_credibleInterval_eq_normalLocationCoverage`: in standardized form the
  coverage is `g(z k_n, β_n)`, where `g(a, c) = Φ(a - c) - Φ(-a - c)` is the mass of
  `[-a, a]` under `N(c, 1)`, `k_n = √(1 + σ²/(n τ²)) > 1` and `β_n = (m₀ - θ₀) σ/(τ² √n)`.

The coverage under the proper prior is **not** below `1 - α` for every `θ₀ ≠ m₀`. As a function
of the truth it is even, strictly decreasing in `|θ₀ - m₀|`
(`normalLocationCoverage_lt_of_abs_lt`), strictly above `1 - α` at `θ₀ = m₀` for `α < 1`
(`one_sub_lt_normalLocationCoverage_self`), hence strictly above `1 - α` also at some `θ₀ ≠ m₀`
(`exists_ne_one_sub_lt_normalLocationCoverage`), and it tends to `0` as `|θ₀ - m₀| → ∞`, so it
falls strictly below `1 - α` far from the prior mean
(`exists_normalLocationCoverage_lt_one_sub`). As `n → ∞` the coverage tends to `1 - α` for every
`θ₀` (`normalLocation_credibleInterval_coverage_of_gaussian`).

## Main definitions

* `PosteriorLimit.normalBandMass`, `PosteriorLimit.normalLocationCoverage`.

## Main results

* `PosteriorLimit.hasLaw_sampleMean_gaussianReal`,
  `PosteriorLimit.hasLaw_posteriorMean_sub_gaussianReal`,
  `PosteriorLimit.measureReal_mem_waldInterval_sampleMean`,
  `PosteriorLimit.measureReal_mem_credibleInterval_normalLocation`,
  `PosteriorLimit.normalBandMass_strictAntiOn`,
  `PosteriorLimit.normalLocationCoverage_lt_of_abs_lt`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open BiasAnalysis.Distributions MetaAnalysis

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### The law of the sample mean -/

/-- **The law of the sample mean of normal data.** For i.i.d. observations with law
`N(θ₀, σ²)`, `σ² > 0`, and `n ≥ 1`, the sample mean `Ȳ_n` has law `N(θ₀, σ²/n)`. This is the
case of equal variances of the law of the inverse variance weighted estimate
(`MetaAnalysis.hasLaw_ivwEstimate`). -/
theorem hasLaw_sampleMean_gaussianReal [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY : IsIIDSample Y P) {θ₀ σ2 : ℝ} (hσ : 0 < σ2)
    (hlaw : P.map (Y 0) = gaussianReal θ₀ σ2.toNNReal) {n : ℕ} (hn : 1 ≤ n) :
    HasLaw (sampleMean id Y n) (gaussianReal θ₀ (σ2 / n).toNNReal) P := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hind : iIndepFun (fun i : Fin (m + 1) ↦ Y i) P := hY.indep.precomp Fin.val_injective
  have hYi : ∀ i : Fin (m + 1),
      HasLaw (Y i) (gaussianReal θ₀ (σ2 * (fun _ : Fin (m + 1) ↦ (1 : ℝ)) i).toNNReal) P :=
    fun i ↦ ⟨(hY.ident i).aemeasurable_fst, by rw [mul_one]; exact (hY.ident i).map_eq.trans hlaw⟩
  have h := hasLaw_ivwEstimate (Fintype.card_fin _) (fun _ ↦ one_pos) hσ hind hYi
  have hfun : (fun ω ↦ ivwEstimate (fun _ : Fin (m + 1) ↦ (1 : ℝ)) (fun i ↦ Y i ω)) =
      sampleMean id Y (m + 1) := by
    funext ω
    simp only [ivwEstimate, PopulationAdjustment.weightedMean, ivWeight, div_one, one_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sampleMean, id]
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ Y i ω), div_eq_inv_mul]
  have hW : ∑ i : Fin (m + 1), ivWeight (fun _ : Fin (m + 1) ↦ (1 : ℝ)) i = ((m + 1 : ℕ) : ℝ) := by
    simp [ivWeight]
  rwa [hfun, hW] at h

/-! ### Normal mass of an interval -/

/-- **Normal mass of an interval.** If `X ~ N(m, s²)`, `s > 0`, and `l ≤ u`, then
`P{l ≤ X ≤ u} = Φ((u - m)/s) - Φ((l - m)/s)`. -/
theorem measureReal_preimage_Icc_of_hasLaw_gaussianReal {X : Ω → ℝ} {m s : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) (hs : 0 < s) (hv : (v : ℝ) = s ^ 2) {l u : ℝ}
    (hlu : l ≤ u) :
    P.real (X ⁻¹' Icc l u) =
      cdf (gaussianReal 0 1) ((u - m) / s) - cdf (gaussianReal 0 1) ((l - m) / s) := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hv
    have : 0 < s ^ 2 := by positivity
    linarith
  have := nullSingletonClass_gaussianReal (μ := m) hv0
  rw [measureReal_def, ← Measure.map_apply_of_aemeasurable hX.aemeasurable measurableSet_Icc,
    hX.map_eq, ← measureReal_def, measureReal_congr (Ioc_ae_eq_Icc (a := l) (b := u)).symm]
  have hsplit := measureReal_union (μ := gaussianReal m v) (s₁ := Iic l) (s₂ := Ioc l u)
    (Set.disjoint_left.2 fun t ht ht' ↦ by
      rw [mem_Iic] at ht
      rw [mem_Ioc] at ht'
      linarith [ht'.1]) measurableSet_Ioc
  rw [Iic_union_Ioc_eq_Iic hlu] at hsplit
  have hu := cdf_gaussianReal_affine m hs hv ((u - m) / s)
  have hl := cdf_gaussianReal_affine m hs hv ((l - m) / s)
  rw [show m + s * ((u - m) / s) = u by field_simp; ring, cdf_eq_real] at hu
  rw [show m + s * ((l - m) / s) = l by field_simp; ring, cdf_eq_real] at hl
  linarith

/-- `Φ(0) = 1/2`. -/
lemma cdf_gaussianReal_zero_one_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have := cdf_gaussianReal_zero_one_neg 0
  rw [neg_zero] at this
  linarith

/-- If `Φ(z) = 1 - α/2` with `α ≤ 1`, then `z ≥ 0`. -/
lemma nonneg_of_cdf_gaussianReal_eq {α z : ℝ} (hz : cdf (gaussianReal 0 1) z = 1 - α / 2)
    (hα : α ≤ 1) : 0 ≤ z := by
  by_contra h
  have := cdf_gaussianReal_strictMono 0 (v := 1) one_ne_zero (not_le.1 h)
  rw [hz, cdf_gaussianReal_zero_one_zero] at this
  linarith

/-- If `Φ(z) = 1 - α/2` with `α < 1`, then `z > 0`. -/
lemma pos_of_cdf_gaussianReal_eq {α z : ℝ} (hz : cdf (gaussianReal 0 1) z = 1 - α / 2)
    (hα : α < 1) : 0 < z := by
  by_contra h
  have := (cdf_gaussianReal_strictMono 0 (v := 1) one_ne_zero).monotone (not_lt.1 h)
  rw [hz, cdf_gaussianReal_zero_one_zero] at this
  linarith

/-! ### The Wald interval and the flat prior -/

/-- **Exact coverage of the Wald interval for normal data.** For i.i.d. observations with law
`N(θ₀, σ²)`, `σ² > 0`, `n ≥ 1`, and `Φ(z) = 1 - α/2` with `α ≤ 1`, the Wald interval
`Ȳ_n ∓ z σ/√n` contains `θ₀` with probability exactly `1 - α`. -/
theorem measureReal_mem_waldInterval_sampleMean [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY : IsIIDSample Y P) {θ₀ σ2 : ℝ} (hσ : 0 < σ2)
    (hlaw : P.map (Y 0) = gaussianReal θ₀ σ2.toNNReal) {n : ℕ} (hn : 1 ≤ n) {α z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) (hα : α ≤ 1) :
    P.real {ω | θ₀ ∈ waldInterval (sampleMean id Y n ω) (√σ2) z n} = 1 - α := by
  have hz0 := nonneg_of_cdf_gaussianReal_eq hz hα
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set s := √σ2 / √n with hs
  have hspos : 0 < s := by positivity
  have hv : (((σ2 / n).toNNReal : ℝ≥0) : ℝ) = s ^ 2 := by
    rw [Real.coe_toNNReal _ (by positivity), hs, div_pow, Real.sq_sqrt hσ.le,
      Real.sq_sqrt hn0.le]
  have hset : {ω | θ₀ ∈ waldInterval (sampleMean id Y n ω) (√σ2) z n} =
      sampleMean id Y n ⁻¹' Icc (θ₀ - z * s) (θ₀ + z * s) := by
    ext ω
    simp only [waldInterval, Set.mem_ofPred_eq, mem_Icc, mem_preimage, hs, mul_div_assoc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset, measureReal_preimage_Icc_of_hasLaw_gaussianReal
    (hasLaw_sampleMean_gaussianReal hY hσ hlaw hn) hspos hv (by nlinarith)]
  rw [show (θ₀ + z * s - θ₀) / s = z by field_simp; ring,
    show (θ₀ - z * s - θ₀) / s = -z by field_simp; ring, cdf_gaussianReal_zero_one_neg, hz]
  ring

/-- **Exact coverage of the flat prior credible interval.** For i.i.d. observations with law
`N(θ₀, σ²)`, `σ² > 0`, `n ≥ 1`, and `Φ(z) = 1 - α/2` with `α ≤ 1`, the equal tailed credible
interval of `N(Ȳ_n, σ²/n)`, the flat prior limit of the normal location posterior, is the Wald
interval and contains `θ₀` with probability exactly `1 - α`. -/
theorem measureReal_mem_credibleInterval_flat [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY : IsIIDSample Y P) {θ₀ σ2 : ℝ} (hσ : 0 < σ2)
    (hlaw : P.map (Y 0) = gaussianReal θ₀ σ2.toNNReal) {n : ℕ} (hn : 1 ≤ n) {α z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) (hα : α ≤ 1) :
    P.real {ω | θ₀ ∈ credibleInterval
      (gaussianReal (sampleMean id Y n ω) (σ2 / n).toNNReal) α} = 1 - α := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hset : {ω | θ₀ ∈ credibleInterval
      (gaussianReal (sampleMean id Y n ω) (σ2 / n).toNNReal) α} =
      {ω | θ₀ ∈ waldInterval (sampleMean id Y n ω) (√σ2) z n} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      credibleInterval_gaussianReal _ (div_pos hσ hn0) hz, Real.sqrt_div' σ2 hn0.le]
    simp only [waldInterval, mem_Icc]
    rw [show z * √σ2 / √n = √σ2 / √n * z by ring]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith [h1, h2]
  rw [hset]
  exact measureReal_mem_waldInterval_sampleMean hY hσ hlaw hn hz hα

/-! ### The proper normal prior -/

/-- The posterior mean with `n ≥ 1` observations of variance `σ²` is the affine function
`m_n = v_n n/σ² Ȳ_n + v_n m₀/τ²` of the sample mean, `v_n = 1/(1/τ² + n/σ²)`. -/
lemma posteriorMean_fin_const_eq_sampleMean {m₀ τ2 σ2 : ℝ} (hτ : 0 < τ2) (hσ : 0 < σ2)
    (Y : ℕ → Ω → ℝ) {n : ℕ} (hn : 1 ≤ n) (ω : Ω) :
    posteriorMean m₀ τ2 (fun _ : Fin n ↦ σ2) (fun i ↦ Y i ω) =
      posteriorVariance τ2 (fun _ : Fin n ↦ σ2) * n / σ2 * sampleMean id Y n ω +
        posteriorVariance τ2 (fun _ : Fin n ↦ σ2) * m₀ / τ2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [posteriorMean_fin_const, posteriorVariance, posteriorPrecision_fin_const, sampleMean,
    Fin.sum_univ_eq_sum_range (fun i ↦ Y i ω)]
  simp only [id]
  have hn' : (n : ℝ) ≠ 0 := hn0.ne'
  have hA : 0 < 1 / τ2 + n / σ2 := by positivity
  field_simp
  ring

/-- **The law of the posterior mean.** For i.i.d. observations with law `N(θ₀, σ²)`, `σ² > 0`,
the prior `N(m₀, τ²)`, `τ² > 0`, and `n ≥ 1`, let `v_n = 1/(1/τ² + n/σ²)`. The posterior mean
minus the truth has law `N(b_n, s_n²)` with `b_n = v_n (m₀ - θ₀)/τ²` and `s_n = v_n √n/σ`. -/
theorem hasLaw_posteriorMean_sub_gaussianReal [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    (hY : IsIIDSample Y P) {m₀ τ2 σ2 θ₀ : ℝ} (hτ : 0 < τ2) (hσ : 0 < σ2)
    (hlaw : P.map (Y 0) = gaussianReal θ₀ σ2.toNNReal) {n : ℕ} (hn : 1 ≤ n) :
    HasLaw (fun ω ↦ posteriorMean m₀ τ2 (fun _ : Fin n ↦ σ2) (fun i ↦ Y i ω) - θ₀)
      (gaussianReal (posteriorVariance τ2 (fun _ : Fin n ↦ σ2) * (m₀ - θ₀) / τ2)
        ((posteriorVariance τ2 (fun _ : Fin n ↦ σ2) * √n / √σ2) ^ 2).toNNReal) P := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set v := posteriorVariance τ2 (fun _ : Fin n ↦ σ2) with hvdef
  have hvA : v = 1 / (1 / τ2 + n / σ2) := by
    rw [hvdef, posteriorVariance, posteriorPrecision_fin_const]
  set κ : ℝ := v * n / σ2 with hκ
  set β0 : ℝ := v * m₀ / τ2 - θ₀ with hβ0
  have hfun : (fun ω ↦ posteriorMean m₀ τ2 (fun _ : Fin n ↦ σ2) (fun i ↦ Y i ω) - θ₀) =
      (fun x ↦ κ * x + β0) ∘ sampleMean id Y n := by
    funext ω
    rw [Function.comp_apply, posteriorMean_fin_const_eq_sampleMean hτ hσ Y hn ω, hκ, hβ0]
    ring
  have hmap : (gaussianReal θ₀ (σ2 / n).toNNReal).map (fun x ↦ κ * x + β0) =
      gaussianReal (κ * θ₀ + β0) (⟨κ ^ 2, sq_nonneg _⟩ * (σ2 / n).toNNReal) := by
    have : (fun x : ℝ ↦ κ * x + β0) = (· + β0) ∘ (κ * ·) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    rfl
  rw [hfun]
  have hW := HasLaw.comp ⟨by fun_prop, hmap⟩ (hasLaw_sampleMean_gaussianReal hY hσ hlaw hn)
  convert hW using 2
  · rw [hβ0, hκ, hvA]
    field_simp
    ring
  · ext
    change _ = κ ^ 2 * (((σ2 / n).toNNReal : ℝ≥0) : ℝ)
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ σ2 / n), Real.coe_toNNReal _ (sq_nonneg _), hκ,
      div_pow, div_pow, mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hσ.le]
    field_simp

/-- **Exact coverage under a proper normal prior.** For i.i.d. observations with law
`N(θ₀, σ²)`, `σ² > 0`, the prior `N(m₀, τ²)`, `τ² > 0`, `n ≥ 1`, and `Φ(z) = 1 - α/2` with
`α ≤ 1`, let `v_n = 1/(1/τ² + n/σ²)` be the posterior variance, and `b_n = v_n (m₀ - θ₀)/τ²`,
`s_n = v_n √n/σ` the mean and the standard deviation of the posterior mean minus the truth
(`hasLaw_posteriorMean_sub_gaussianReal`). The equal tailed credible interval of the posterior
contains `θ₀` with probability exactly `Φ((z√v_n - b_n)/s_n) - Φ((-z√v_n - b_n)/s_n)`. -/
theorem measureReal_mem_credibleInterval_normalLocation [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ} (hY : IsIIDSample Y P) {m₀ τ2 σ2 θ₀ : ℝ} (hτ : 0 < τ2) (hσ : 0 < σ2)
    (hlaw : P.map (Y 0) = gaussianReal θ₀ σ2.toNNReal) {n : ℕ} (hn : 1 ≤ n) {α z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) (hα : α ≤ 1) :
    P.real {ω | θ₀ ∈ credibleInterval (normalLocationPosterior m₀ τ2 σ2 Y n ω) α} =
      cdf (gaussianReal 0 1)
          ((z * √(posteriorVariance τ2 (fun _ : Fin n ↦ σ2)) -
              posteriorVariance τ2 (fun _ : Fin n ↦ σ2) * (m₀ - θ₀) / τ2) /
            (posteriorVariance τ2 (fun _ : Fin n ↦ σ2) * √n / √σ2)) -
        cdf (gaussianReal 0 1)
          ((-(z * √(posteriorVariance τ2 (fun _ : Fin n ↦ σ2))) -
              posteriorVariance τ2 (fun _ : Fin n ↦ σ2) * (m₀ - θ₀) / τ2) /
            (posteriorVariance τ2 (fun _ : Fin n ↦ σ2) * √n / √σ2)) := by
  have hz0 := nonneg_of_cdf_gaussianReal_eq hz hα
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hvpos := posteriorVariance_fin_const_pos hτ hσ n
  set v := posteriorVariance τ2 (fun _ : Fin n ↦ σ2) with hvdef
  have hspos : 0 < v * √n / √σ2 := by
    have h3 : 0 < √σ2 := Real.sqrt_pos.2 hσ
    have h4 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
    positivity
  have hw0 : 0 ≤ z * √v := by positivity
  have hset : {ω | θ₀ ∈ credibleInterval (normalLocationPosterior m₀ τ2 σ2 Y n ω) α} =
      (fun ω ↦ posteriorMean m₀ τ2 (fun _ : Fin n ↦ σ2) (fun i ↦ Y i ω) - θ₀) ⁻¹'
        Icc (-(z * √v)) (z * √v) := by
    ext ω
    rw [Set.mem_ofPred_eq, normalLocation_credibleInterval hτ hσ Y n ω hz, mem_preimage,
      mem_Icc, mem_Icc, ← hvdef]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith [h1, h2]
  rw [hset, measureReal_preimage_Icc_of_hasLaw_gaussianReal
    (hasLaw_posteriorMean_sub_gaussianReal hY hτ hσ hlaw hn) hspos
    (Real.coe_toNNReal _ (sq_nonneg _)) (by linarith)]

/-- The mass `Φ(a - c) - Φ(-a - c)` of `[-a, a]` under `N(c, 1)`, the probability that
`|Z + c| ≤ a` for a standard normal `Z`. -/
noncomputable def normalBandMass (a c : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) (a - c) - cdf (gaussianReal 0 1) (-a - c)

/-- The coverage of the equal tailed credible interval under the prior `N(m₀, τ²)` for data
`N(θ₀, σ²)` of size `n`, in standardized form: `g(z k_n, β_n)` with
`k_n = √(1 + σ²/(n τ²))` and `β_n = (m₀ - θ₀) σ/(τ² √n)`. -/
noncomputable def normalLocationCoverage (m₀ τ2 σ2 z : ℝ) (n : ℕ) (θ₀ : ℝ) : ℝ :=
  normalBandMass (z * √(1 + σ2 / (n * τ2))) ((m₀ - θ₀) * √σ2 / (τ2 * √n))

/-- **The coverage in standardized form.** Under the hypotheses of
`measureReal_mem_credibleInterval_normalLocation`, the coverage of the credible interval is
`normalLocationCoverage m₀ τ² σ² z n θ₀ = g(z √(1 + σ²/(n τ²)), (m₀ - θ₀) σ/(τ² √n))`. -/
theorem measureReal_mem_credibleInterval_eq_normalLocationCoverage [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ} (hY : IsIIDSample Y P) {m₀ τ2 σ2 θ₀ : ℝ} (hτ : 0 < τ2) (hσ : 0 < σ2)
    (hlaw : P.map (Y 0) = gaussianReal θ₀ σ2.toNNReal) {n : ℕ} (hn : 1 ≤ n) {α z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) (hα : α ≤ 1) :
    P.real {ω | θ₀ ∈ credibleInterval (normalLocationPosterior m₀ τ2 σ2 Y n ω) α} =
      normalLocationCoverage m₀ τ2 σ2 z n θ₀ := by
  rw [measureReal_mem_credibleInterval_normalLocation hY hτ hσ hlaw hn hz hα,
    normalLocationCoverage, normalBandMass]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set v := posteriorVariance τ2 (fun _ : Fin n ↦ σ2) with hvdef
  have hvA : v = 1 / (1 / τ2 + n / σ2) := by
    rw [hvdef, posteriorVariance, posteriorPrecision_fin_const]
  have hvpos : 0 < v := by rw [hvA]; positivity
  have h3 : 0 < √σ2 := Real.sqrt_pos.2 hσ
  have h4 : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hk : √v / (v * √n / √σ2) = √(1 + σ2 / (n * τ2)) := by
    have hsv : 0 < √v := Real.sqrt_pos.2 hvpos
    have e1 : √v * √v = v := Real.mul_self_sqrt hvpos.le
    have step1 : √v / (v * √n / √σ2) = √σ2 / (√v * √n) := by
      rw [div_div_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
      linear_combination (√σ2 * √n) * e1
    have step2 : √σ2 / (√v * √n) = √(σ2 / (v * n)) := by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul hvpos.le]
    have step3 : σ2 / (v * n) = 1 + σ2 / (n * τ2) := by
      rw [hvA]
      field_simp
      ring
    rw [step1, step2, step3]
  have hβ : v * (m₀ - θ₀) / τ2 / (v * √n / √σ2) = (m₀ - θ₀) * √σ2 / (τ2 * √n) := by
    field_simp
  have hsplit : ∀ sgn : ℝ, (sgn * (z * √v) - v * (m₀ - θ₀) / τ2) / (v * √n / √σ2) =
      sgn * (z * (√v / (v * √n / √σ2))) - v * (m₀ - θ₀) / τ2 / (v * √n / √σ2) := by
    intro sgn
    field_simp
  have e1 := hsplit 1
  have e2 := hsplit (-1)
  simp only [one_mul, neg_one_mul] at e1 e2
  rw [e1, e2, hk, hβ]

/-! ### The shape of the coverage -/

/-- The standard normal distribution function increases by the integral of the density. -/
lemma cdf_gaussianReal_sub_eq_integral {x y : ℝ} (hxy : x ≤ y) :
    cdf (gaussianReal 0 1) y - cdf (gaussianReal 0 1) x =
      ∫ t in x..y, gaussianPDFReal 0 1 t := by
  have := nullSingletonClass_gaussianReal (μ := 0) (one_ne_zero (α := ℝ≥0))
  have hsplit := measureReal_union (μ := gaussianReal 0 1) (s₁ := Iic x) (s₂ := Ioc x y)
    (Set.disjoint_left.2 fun t ht ht' ↦ by
      rw [mem_Iic] at ht
      rw [mem_Ioc] at ht'
      linarith [ht'.1]) measurableSet_Ioc
  rw [Iic_union_Ioc_eq_Iic hxy] at hsplit
  rw [cdf_eq_real, cdf_eq_real, hsplit, intervalIntegral.integral_of_le hxy, add_sub_cancel_left,
    measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc
      fun t _ ↦ gaussianPDFReal_nonneg 0 1 t)]

/-- The standard normal density is larger at the point closer to the origin. -/
lemma gaussianPDFReal_lt_of_abs_lt {x y : ℝ} (h : |x| < |y|) :
    gaussianPDFReal 0 1 y < gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) (by positivity)
  have : x ^ 2 < y ^ 2 := sq_lt_sq.2 h
  linarith

/-- `g(a, ·)` is even. -/
lemma normalBandMass_neg (a c : ℝ) : normalBandMass a (-c) = normalBandMass a c := by
  simp only [normalBandMass]
  have h1 := cdf_gaussianReal_zero_one_neg (-a - c)
  have h2 := cdf_gaussianReal_zero_one_neg (a - c)
  rw [show -(-a - c) = a - -c by ring] at h1
  rw [show -(a - c) = -a - -c by ring] at h2
  linarith

/-- `g(a, 0) = 2 Φ(a) - 1`. -/
lemma normalBandMass_zero (a : ℝ) : normalBandMass a 0 = 2 * cdf (gaussianReal 0 1) a - 1 := by
  have := cdf_gaussianReal_zero_one_neg a
  simp only [normalBandMass, sub_zero]
  linarith

/-- **Anderson's inequality on the line.** For `a > 0`, `g(a, ·)` is strictly decreasing on
`[0, ∞)`: shifting the band `[-a, a]` away from the center of the standard normal law lowers its
mass. -/
theorem normalBandMass_strictAntiOn {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (normalBandMass a) (Ici 0) := by
  intro c₁ hc₁ c₂ _ h12
  rw [mem_Ici] at hc₁
  have hint : ∀ u w : ℝ, IntervalIntegrable (gaussianPDFReal 0 1) volume u w := fun u w ↦
    (integrable_gaussianPDFReal 0 1).intervalIntegrable
  have hint2 : ∀ u w : ℝ, IntervalIntegrable (fun t ↦ gaussianPDFReal 0 1 (t - 2 * a)) volume u w :=
    fun u w ↦ ((integrable_gaussianPDFReal 0 1).comp_sub_right (2 * a)).intervalIntegrable
  have e1 := cdf_gaussianReal_sub_eq_integral (show a - c₂ ≤ a - c₁ by linarith)
  have e2 := cdf_gaussianReal_sub_eq_integral (show -a - c₂ ≤ -a - c₁ by linarith)
  have hshift : ∫ t in (-a - c₂)..(-a - c₁), gaussianPDFReal 0 1 t =
      ∫ t in (a - c₂)..(a - c₁), gaussianPDFReal 0 1 (t - 2 * a) := by
    rw [intervalIntegral.integral_comp_sub_right]
    congr 1 <;> ring
  have hpos : 0 < ∫ t in (a - c₂)..(a - c₁),
      (gaussianPDFReal 0 1 t - gaussianPDFReal 0 1 (t - 2 * a)) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht ↦ ?_) (by linarith)
    · exact (hint _ _).sub (hint2 _ _)
    · rw [sub_pos]
      refine gaussianPDFReal_lt_of_abs_lt ?_
      have hta : t < a := by linarith [ht.2]
      exact sq_lt_sq.1 (by nlinarith [mul_pos ha (show 0 < a - t by linarith)])
  rw [intervalIntegral.integral_sub (hint _ _) (hint2 _ _), ← e1,
    ← hshift, ← e2] at hpos
  simp only [normalBandMass]
  linarith

/-- `g(a, ·)` is strictly decreasing in `|c|` for `a > 0`. -/
theorem normalBandMass_lt_of_abs_lt {a c₁ c₂ : ℝ} (ha : 0 < a) (h : |c₁| < |c₂|) :
    normalBandMass a c₂ < normalBandMass a c₁ := by
  have e : ∀ c, normalBandMass a c = normalBandMass a |c| := fun c ↦ by
    rcases le_total 0 c with hc | hc
    · rw [abs_of_nonneg hc]
    · rw [abs_of_nonpos hc, normalBandMass_neg]
  rw [e c₁, e c₂]
  exact normalBandMass_strictAntiOn ha (mem_Ici.2 (abs_nonneg _)) (mem_Ici.2 (abs_nonneg _)) h

lemma continuous_normalBandMass (a : ℝ) : Continuous (normalBandMass a) := by
  unfold normalBandMass
  exact (continuous_cdf_gaussianReal_zero_one.comp (continuous_const.sub continuous_id)).sub
    (continuous_cdf_gaussianReal_zero_one.comp (continuous_const.sub continuous_id))

/-- `g(a, c) → 0` as `c → ∞`. -/
lemma tendsto_normalBandMass_atTop (a : ℝ) : Tendsto (normalBandMass a) atTop (𝓝 0) := by
  have h1 : Tendsto (fun c : ℝ ↦ a - c) atTop atBot :=
    (tendsto_atBot_add_const_left atTop a tendsto_neg_atTop_atBot).congr fun c ↦ by ring
  have h2 : Tendsto (fun c : ℝ ↦ -a - c) atTop atBot :=
    (tendsto_atBot_add_const_left atTop (-a) tendsto_neg_atTop_atBot).congr fun c ↦ by ring
  have := ((tendsto_cdf_atBot (gaussianReal 0 1)).comp h1).sub
    ((tendsto_cdf_atBot (gaussianReal 0 1)).comp h2)
  rw [sub_zero] at this
  exact this

/-! ### Coverage as a function of the truth -/

section Coverage

variable {m₀ τ2 σ2 α z : ℝ} {n : ℕ}

lemma one_lt_sqrt_one_add {τ2 σ2 : ℝ} (hτ : 0 < τ2) (hσ : 0 < σ2) {n : ℕ} (hn : 1 ≤ n) :
    1 < √(1 + σ2 / (n * τ2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < σ2 / (n * τ2) := by positivity
  exact (Real.lt_sqrt zero_le_one).2 (by linarith)

/-- **Coverage above the nominal level at the prior mean.** For `α < 1` and `θ₀ = m₀` the
coverage is `2 Φ(z k_n) - 1 > 2 Φ(z) - 1 = 1 - α`. -/
theorem one_sub_lt_normalLocationCoverage_self (hτ : 0 < τ2) (hσ : 0 < σ2) (hn : 1 ≤ n)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) (hα : α < 1) :
    1 - α < normalLocationCoverage m₀ τ2 σ2 z n m₀ := by
  have hz0 := pos_of_cdf_gaussianReal_eq hz hα
  have hk := one_lt_sqrt_one_add hτ hσ hn
  rw [normalLocationCoverage, sub_self, zero_mul, zero_div, normalBandMass_zero]
  have := cdf_gaussianReal_strictMono 0 (v := 1) one_ne_zero
    (show z < z * √(1 + σ2 / (n * τ2)) by nlinarith)
  rw [hz] at this
  linarith

/-- **The coverage decreases with the distance of the truth from the prior mean.** For `z > 0`,
if `|θ₀ - m₀| < |θ₁ - m₀|` then the coverage at `θ₁` is strictly below the coverage at `θ₀`. -/
theorem normalLocationCoverage_lt_of_abs_lt (hτ : 0 < τ2) (hσ : 0 < σ2) (hn : 1 ≤ n)
    (hz : 0 < z) {θ₀ θ₁ : ℝ} (h : |θ₀ - m₀| < |θ₁ - m₀|) :
    normalLocationCoverage m₀ τ2 σ2 z n θ₁ < normalLocationCoverage m₀ τ2 σ2 z n θ₀ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk := one_lt_sqrt_one_add hτ hσ hn
  refine normalBandMass_lt_of_abs_lt (by nlinarith) ?_
  have hc : 0 < √σ2 / (τ2 * √n) := by
    have : 0 < √σ2 := Real.sqrt_pos.2 hσ
    have : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
    positivity
  rw [mul_div_assoc, mul_div_assoc, abs_mul, abs_mul, abs_of_pos hc, abs_sub_comm m₀,
    abs_sub_comm m₀]
  exact mul_lt_mul_of_pos_right h hc

lemma continuous_normalLocationCoverage (m₀ τ2 σ2 z : ℝ) (n : ℕ) :
    Continuous (normalLocationCoverage m₀ τ2 σ2 z n) :=
  (continuous_normalBandMass _).comp (by fun_prop)

/-- **Coverage above the nominal level away from the prior mean.** For `α < 1` there is a truth
`θ₀ ≠ m₀` at which the coverage of the credible interval under the prior `N(m₀, τ²)` is strictly
above `1 - α`. -/
theorem exists_ne_one_sub_lt_normalLocationCoverage (hτ : 0 < τ2) (hσ : 0 < σ2) (hn : 1 ≤ n)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) (hα : α < 1) :
    ∃ θ₀, θ₀ ≠ m₀ ∧ 1 - α < normalLocationCoverage m₀ τ2 σ2 z n θ₀ := by
  have hev := (continuous_normalLocationCoverage m₀ τ2 σ2 z n).continuousAt.eventually
    (lt_mem_nhds (one_sub_lt_normalLocationCoverage_self (m₀ := m₀) hτ hσ hn hz hα))
  obtain ⟨θ₀, h1, h2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ θ in 𝓝[≠] m₀, θ ∈ ({m₀}ᶜ : Set ℝ))).exists
  exact ⟨θ₀, h2, h1⟩

/-- **Undercoverage far from the prior mean.** The coverage tends to `0` as `θ₀ → ∞`; in
particular, for `α < 1` there is a truth at which it is strictly below `1 - α`. -/
theorem exists_normalLocationCoverage_lt_one_sub (hτ : 0 < τ2) (hσ : 0 < σ2) (hn : 1 ≤ n)
    (hα : α < 1) :
    Tendsto (normalLocationCoverage m₀ τ2 σ2 z n) atTop (𝓝 0) ∧
      ∃ θ₀, normalLocationCoverage m₀ τ2 σ2 z n θ₀ < 1 - α := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < √σ2 / (τ2 * √n) := by
    have : 0 < √σ2 := Real.sqrt_pos.2 hσ
    have : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
    positivity
  have hlin : Tendsto (fun θ₀ : ℝ ↦ (m₀ - θ₀) * √σ2 / (τ2 * √n)) atTop atBot := by
    have : Tendsto (fun θ₀ : ℝ ↦ (θ₀ - m₀) * (√σ2 / (τ2 * √n))) atTop atTop :=
      (tendsto_atTop_add_const_right _ _ tendsto_id).atTop_mul_const hc
    exact (tendsto_neg_atTop_atBot.comp this).congr fun θ₀ ↦ by
      simp only [Function.comp_apply]; ring
  have hlim : Tendsto (normalLocationCoverage m₀ τ2 σ2 z n) atTop (𝓝 0) := by
    have := (tendsto_normalBandMass_atTop (z * √(1 + σ2 / (n * τ2)))).comp
      (tendsto_neg_atBot_atTop.comp hlin)
    refine this.congr fun θ₀ ↦ ?_
    simp only [Function.comp_apply, normalLocationCoverage, normalBandMass_neg]
  refine ⟨hlim, ?_⟩
  exact (hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - α))).exists

end Coverage

/-! ### A computed instance -/

/-- **A computed instance.** Prior `N(m₀, 1/3)`, known variance `σ² = 1`, one observation: the
posterior variance is `1/4`, the band factor is `k_1 = 2`, the bias term is `β_1 = 3 (m₀ - θ₀)`,
and the coverage of the credible interval is `Φ(2z - 3(m₀ - θ₀)) - Φ(-2z - 3(m₀ - θ₀))`, equal
to `2 Φ(2z) - 1` at `θ₀ = m₀`. The critical value `z = q(1 - α/2)` of the standard normal law
solves `Φ(z) = 1 - α/2` for `α ∈ (0, 2)`, and an i.i.d. sample with law `N(θ₀, 1)` exists, so
the hypotheses of the coverage theorems are met. -/
theorem normalLocationCoverage_numeric (m₀ θ₀ z : ℝ) :
    posteriorVariance (1 / 3) (fun _ : Fin 1 ↦ (1 : ℝ)) = 1 / 4 ∧
      normalLocationCoverage m₀ (1 / 3) 1 z 1 θ₀ =
        cdf (gaussianReal 0 1) (2 * z - 3 * (m₀ - θ₀)) -
          cdf (gaussianReal 0 1) (-(2 * z) - 3 * (m₀ - θ₀)) ∧
      normalLocationCoverage m₀ (1 / 3) 1 z 1 m₀ = 2 * cdf (gaussianReal 0 1) (2 * z) - 1 ∧
      (∀ α ∈ Ioo (0 : ℝ) 2, cdf (gaussianReal 0 1) (quantile (gaussianReal 0 1) (1 - α / 2)) =
        1 - α / 2) ∧
      ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ Y : ℕ → Ω → ℝ,
        IsProbabilityMeasure P ∧ IsIIDSample Y P ∧
          P.map (Y 0) = gaussianReal θ₀ (1 : ℝ).toNNReal := by
  have hk : √(1 + (1 : ℝ) / ((1 : ℕ) * (1 / 3))) = 2 := by
    rw [show (1 + (1 : ℝ) / ((1 : ℕ) * (1 / 3))) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hβ : ∀ θ : ℝ, (m₀ - θ) * √(1 : ℝ) / (1 / 3 * √((1 : ℕ) : ℝ)) = 3 * (m₀ - θ) := by
    intro θ
    simp only [Real.sqrt_one, Nat.cast_one]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [posteriorVariance, posteriorPrecision_fin_const]
    norm_num
  · rw [normalLocationCoverage, hk, hβ, normalBandMass]
    ring_nf
  · rw [normalLocationCoverage, hk, hβ, sub_self, mul_zero, normalBandMass_zero]
    ring_nf
  · intro α hα
    exact cdf_quantile ⟨by linarith [hα.2], by linarith [hα.1]⟩
      continuous_cdf_gaussianReal_zero_one
  · obtain ⟨Ω, mΩ, P, Y, hP, -, hY, hlaw⟩ := exists_isIIDSample (gaussianReal θ₀ (1 : ℝ).toNNReal)
    exact ⟨Ω, mΩ, P, Y, hP, hY, (hlaw 0).map_eq⟩

end PosteriorLimit

end CausalInference
