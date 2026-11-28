/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.InformationInequality
public import CausalInference.Estimation.MEstimator
public import CausalInference.Estimation.BernoulliFamily

/-!
# Maximum likelihood estimators and their consistency

The likelihood of the first `n` observations of a sample is `L_n(θ) = ∏_{i < n} f(O_i;θ)`, and a
maximum likelihood estimator over a parameter set `K` is a sequence `θh n` that almost surely
lies in `K` and maximizes `L_n` over `K`. On a compact `K ⊆ Θ`, the maximum likelihood estimator
is an M-estimator for the criterion `θ ↦ n⁻¹ ∑_{i < n} log f(O_i;θ)`, whose limit
`θ ↦ E_θ₀[log f(X;θ)]` has the unique maximizer `θ₀` by the information inequality. The uniform
law of large numbers (`CausalInference.uniform_law_of_large_numbers_real`) and the consistency of
M-estimators (`CausalInference.mEstimator_tendstoInMeasure`) then give consistency.

## Main definitions

* `CausalInference.ParametricFamily.likelihood`: `L_n(θ)` of a sample.
* `CausalInference.ParametricFamily.IsMLE`: maximum likelihood estimators over `K`.

## Main results

* `CausalInference.ParametricFamily.tendstoInMeasure_of_isMLE`: consistency of the maximum
  likelihood estimator over a compact `K ⊆ Θ`, for a parameter in any second countable metric
  space (a scalar or a vector parameter); `isConsistent_of_isMLE` is the scalar form with
  `CausalInference.IsConsistent`.
* `CausalInference.ParametricFamily.bernoulli_pointIdentified` and
  `bernoulli_klDiv_eq_zero_iff`: the Bernoulli parameter is identified.
* `CausalInference.ParametricFamily.bernoulli_isMLE` and `bernoulli_clip_isConsistent`: the
  sample proportion clipped to `[ε, 1 - ε]` is a maximum likelihood estimator over that interval,
  and it is consistent.

References: A. Wald (1949), *Note on the consistency of the maximum likelihood estimate*, Annals
of Mathematical Statistics; A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology InformationTheory
open scoped ENNReal

namespace CausalInference

namespace ParametricFamily

variable {P S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- The likelihood `L_n(θ) = ∏_{i < n} f(O_i;θ)` of the first `n` observations. -/
noncomputable def likelihood (F : ParametricFamily P S) (O : ℕ → Ω → S) (n : ℕ) (ω : Ω)
    (θ : P) : ℝ :=
  ∏ i ∈ Finset.range n, F.density θ (O i ω)

/-- `θh` is a maximum likelihood estimator over `K`: for every `n`, almost surely, `θh n ∈ K`
and `θh n` maximizes the likelihood `L_n` of the first `n` observations over `K`. Any choice of
maximizer for each sample qualifies; no measurability of `θh n` is required. -/
def IsMLE (F : ParametricFamily P S) (μ : Measure Ω) (K : Set P) (O : ℕ → Ω → S)
    (θh : ℕ → Ω → P) : Prop :=
  ∀ n, ∀ᵐ ω ∂μ, θh n ω ∈ K ∧ ∀ θ ∈ K, F.likelihood O n ω θ ≤ F.likelihood O n ω (θh n ω)

variable {F : ParametricFamily P S}

omit [MeasurableSpace Ω] in
/-- On a sample where the densities are positive, the likelihood order is the order of the
average log-likelihoods `n⁻¹ ∑_{i < n} log f(O_i;θ)` (`CausalInference.sampleMean`). -/
theorem sampleMean_logLik_le_of_likelihood_le {O : ℕ → Ω → S} {n : ℕ} {ω : Ω} {θ θ' : P}
    (hθ : ∀ i ∈ Finset.range n, 0 < F.density θ (O i ω))
    (hθ' : ∀ i ∈ Finset.range n, 0 < F.density θ' (O i ω))
    (hL : F.likelihood O n ω θ ≤ F.likelihood O n ω θ') :
    sampleMean (F.logLik θ) O n ω ≤ sampleMean (F.logLik θ') O n ω := by
  have hp : 0 < F.likelihood O n ω θ := Finset.prod_pos hθ
  have hlog := Real.log_le_log hp hL
  simp only [likelihood] at hlog
  rw [Real.log_prod (fun i hi ↦ (hθ i hi).ne'), Real.log_prod (fun i hi ↦ (hθ' i hi).ne')]
    at hlog
  simp only [sampleMean, logLik]
  exact mul_le_mul_of_nonneg_left hlog (inv_nonneg.2 (Nat.cast_nonneg n))

/-- **Consistency of the maximum likelihood estimator.** Let `O` be an i.i.d. sample
(`CausalInference.IsIIDSample`) with law `P_θ₀`, and let `K ⊆ Θ` be compact with `θ₀ ∈ K`, in a
second countable metric parameter space. Assume: the parameter is point identified on `K` from
the law; `θ ↦ f(x;θ)` is continuous on `K` for `ν`-almost every `x`; almost surely under `P_θ₀`,
`f(X;θ) > 0` for all `θ ∈ K`; and `|log f(X;θ)| ≤ H(X)` on `K` for a `P_θ₀`-integrable `H`. Then
every maximum likelihood estimator over `K` converges to `θ₀` in probability.

Proof: the information inequality makes `θ₀` the unique maximizer of `θ ↦ E_θ₀[log f(X;θ)]` on
`K`; on the almost sure event where all densities at the observations are positive, a maximizer of
the likelihood maximizes the average log-likelihood; `mEstimator_tendstoInMeasure` concludes. -/
theorem tendstoInMeasure_of_isMLE [MetricSpace P] [SecondCountableTopology P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {O : ℕ → Ω → S} (hO : IsIIDSample O μ) {θ₀ : P}
    (hlaw : μ.map (O 0) = F.law θ₀) {K : Set P} (hK : IsCompact K) (hKΘ : K ⊆ F.Θ)
    (hθ₀ : θ₀ ∈ K) (hid : PointIdentified K F.law id)
    (hcont : ∀ᵐ x ∂F.ν, ContinuousOn (fun θ ↦ F.density θ x) K)
    (hpos : ∀ᵐ x ∂F.law θ₀, ∀ θ ∈ K, 0 < F.density θ x) {H : S → ℝ}
    (hH : Integrable H (F.law θ₀)) (hdom : ∀ᵐ x ∂F.law θ₀, ∀ θ ∈ K, |F.logLik θ x| ≤ H x)
    {θh : ℕ → Ω → P} (hmle : F.IsMLE μ K O θh) :
    TendstoInMeasure μ θh atTop (fun _ ↦ θ₀) := by
  have hθ₀Θ := hKΘ hθ₀
  have hcont' : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (fun θ ↦ F.logLik θ z) K := by
    rw [hlaw]
    filter_upwards [ae_law_of_ae hcont, hpos] with x hc hp
    exact hc.log fun θ hθ ↦ (hp θ hθ).ne'
  have hlogint : ∀ θ ∈ K, Integrable (F.logLik θ) (F.law θ₀) := fun θ hθ ↦
    hH.mono' (F.measurable_density θ).log.aestronglyMeasurable (by
      filter_upwards [hdom] with x hx
      rw [Real.norm_eq_abs]
      exact hx θ hθ)
  refine mEstimator_tendstoInMeasure hO hK (m := fun z θ ↦ F.logLik θ z)
    (fun θ _ ↦ (F.measurable_density θ).log) hcont' (H := H) (by rw [hlaw]; exact hH)
    (by rw [hlaw]; exact hdom) hθ₀ ?_ ?_ ?_
  · intro θ hθ hne
    rw [hlaw]
    have hposθ : ∀ᵐ x ∂F.law θ₀, 0 < F.density θ x := hpos.mono fun x hx ↦ hx θ hθ
    obtain ⟨hle, heq⟩ :=
      integral_logLik_le hθ₀Θ (hKΘ hθ) hposθ (hlogint θ₀ hθ₀) (hlogint θ hθ)
    exact lt_of_le_of_ne hle fun h ↦ hne (hid θ hθ θ₀ hθ₀ (heq h))
  · exact (WithProbTendingToOne.of_ae (ae_all_iff.2 fun n ↦ (hmle n).mono fun ω h ↦ h.1)).mono
      fun n ω h ↦ h n
  · intro δ hδ
    have hsample : ∀ᵐ ω ∂μ, ∀ i, ∀ θ ∈ K, 0 < F.density θ (O i ω) :=
      hO.ae_forall (by rw [hlaw]; exact hpos)
    refine (WithProbTendingToOne.of_ae ((ae_all_iff.2 hmle).and hsample)).mono
      fun n ω hω ↦ ?_
    obtain ⟨hm, hs⟩ := hω
    have := sampleMean_logLik_le_of_likelihood_le (fun i _ ↦ hs i θ₀ hθ₀)
      (fun i _ ↦ hs i _ (hm n).1) ((hm n).2 θ₀ hθ₀)
    exact le_trans this (le_add_of_nonneg_right hδ.le)

/-- **Consistency of the maximum likelihood estimator, scalar parameter**: under the hypotheses
of `tendstoInMeasure_of_isMLE`, a maximum likelihood estimator over `K` is consistent for `θ₀`
(`CausalInference.IsConsistent`). -/
theorem isConsistent_of_isMLE {F : ParametricFamily ℝ S} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {O : ℕ → Ω → S} (hO : IsIIDSample O μ) {θ₀ : ℝ}
    (hlaw : μ.map (O 0) = F.law θ₀) {K : Set ℝ} (hK : IsCompact K) (hKΘ : K ⊆ F.Θ)
    (hθ₀ : θ₀ ∈ K) (hid : PointIdentified K F.law id)
    (hcont : ∀ᵐ x ∂F.ν, ContinuousOn (fun θ ↦ F.density θ x) K)
    (hpos : ∀ᵐ x ∂F.law θ₀, ∀ θ ∈ K, 0 < F.density θ x) {H : S → ℝ}
    (hH : Integrable H (F.law θ₀)) (hdom : ∀ᵐ x ∂F.law θ₀, ∀ θ ∈ K, |F.logLik θ x| ≤ H x)
    {θh : ℕ → Ω → ℝ} (hmle : F.IsMLE μ K O θh) : IsConsistent θh θ₀ μ :=
  tendstoInMeasure_of_isMLE hO hlaw hK hKΘ hθ₀ hid hcont hpos hH hdom hmle

/-! ### The Bernoulli family -/

/-- The Bernoulli parameter is point identified from the law: the density at a success is the
parameter. -/
theorem bernoulli_pointIdentified : PointIdentified bernoulli.Θ bernoulli.law id := by
  rw [pointIdentified_law_iff]
  intro p _ q _ h
  simpa [bernoulli] using Measure.ae_count_iff.1 h true

/-- `KL(P_p ‖ P_q) = 0` if and only if `p = q`, for `p, q ∈ (0, 1)`. -/
theorem bernoulli_klDiv_eq_zero_iff {p q : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) : klDiv (bernoulli.law p) (bernoulli.law q) = 0 ↔ q = p :=
  klDiv_law_eq_zero_iff bernoulli_pointIdentified hp hq

/-- The two point Gibbs inequality: for `a, p ∈ (0, 1)`,
`a log p + (1 - a) log (1 - p) ≤ a log a + (1 - a) log (1 - a)`. -/
theorem crossEntropy_le_entropy {a p : ℝ} (ha : 0 < a) (ha1 : a < 1) (hp : 0 < p)
    (hp1 : p < 1) :
    a * Real.log p + (1 - a) * Real.log (1 - p) ≤
      a * Real.log a + (1 - a) * Real.log (1 - a) := by
  have h1 := mul_log_sub_log_le ha hp
  have h2 := mul_log_sub_log_le (sub_pos.2 ha1) (sub_pos.2 hp1)
  nlinarith [h1, h2]

/-- For `0 < ε ≤ 1/2`, the function `p ↦ a log p + (1 - a) log (1 - p)` on `[ε, 1 - ε]` is
maximized at `a` clipped to `[ε, 1 - ε]`, for every real `a`. Inside the interval this is
`crossEntropy_le_entropy`; below it, the function at `p` is at most its value at `ε`, which is
the inside case for `a = ε`, and symmetrically above it. -/
theorem crossEntropy_le_clip {ε a p : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hp : p ∈ Set.Icc ε (1 - ε)) :
    a * Real.log p + (1 - a) * Real.log (1 - p) ≤
      a * Real.log (max ε (min (1 - ε) a)) +
        (1 - a) * Real.log (1 - max ε (min (1 - ε) a)) := by
  obtain ⟨hp1, hp2⟩ := hp
  have hp0 : 0 < p := hε.trans_le hp1
  have hpl : p < 1 := by linarith
  rcases lt_or_ge a ε with hlo | hlo
  · have hq : max ε (min (1 - ε) a) = ε := by
      rw [min_eq_right (by linarith), max_eq_left hlo.le]
    rw [hq]
    have hin := crossEntropy_le_entropy hε (by linarith) hp0 hpl
    have hA : 0 ≤ Real.log p - Real.log ε := sub_nonneg.2 (Real.log_le_log hε hp1)
    have hB : Real.log (1 - p) - Real.log (1 - ε) ≤ 0 :=
      sub_nonpos.2 (Real.log_le_log (by linarith) (by linarith))
    have e1 := mul_le_mul_of_nonneg_right hlo.le hA
    have e2 := mul_le_mul_of_nonpos_right (show 1 - ε ≤ 1 - a by linarith) hB
    nlinarith [e1, e2, hin]
  rcases le_or_gt a (1 - ε) with hhi | hhi
  · have hq : max ε (min (1 - ε) a) = a := by
      rw [min_eq_right hhi, max_eq_right hlo]
    rw [hq]
    exact crossEntropy_le_entropy (hε.trans_le hlo) (by linarith) hp0 hpl
  · have hq : max ε (min (1 - ε) a) = 1 - ε := by
      rw [min_eq_left hhi.le, max_eq_right (by linarith)]
    rw [hq]
    have hin := crossEntropy_le_entropy (a := 1 - ε) (by linarith) (by linarith) hp0 hpl
    rw [sub_sub_cancel] at hin
    have hA : Real.log p - Real.log (1 - ε) ≤ 0 :=
      sub_nonpos.2 (Real.log_le_log hp0 hp2)
    have hB : 0 ≤ Real.log (1 - p) - Real.log ε :=
      sub_nonneg.2 (Real.log_le_log hε (by linarith))
    have e1 := mul_le_mul_of_nonpos_right hhi.le hA
    have e2 := mul_le_mul_of_nonneg_right (show 1 - a ≤ ε by linarith) hB
    rw [sub_sub_cancel]
    nlinarith [e1, e2, hin]

/-- `[ε, 1 - ε] ⊆ (0, 1)` for `ε > 0`. -/
theorem Icc_subset_bernoulli_Θ {ε : ℝ} (hε : 0 < ε) : Set.Icc ε (1 - ε) ⊆ bernoulli.Θ :=
  fun _ hp ↦ ⟨hε.trans_le hp.1, by linarith [hp.2]⟩

/-- The Bernoulli log density: `log f(x;p) = T(x) log p + (1 - T(x)) log (1 - p)`. -/
theorem bernoulli_log_density (p : ℝ) (x : Bool) :
    Real.log (bernoulli.density p x) =
      successIndicator x * Real.log p + (1 - successIndicator x) * Real.log (1 - p) := by
  cases x <;> simp [bernoulli, successIndicator]

/-- **The clipped sample proportion is a maximum likelihood estimator** over `[ε, 1 - ε]`, for
`0 < ε ≤ 1/2`. With `k` successes in `n` trials and `a = k / n`,
`log L_n(p) = n (a log p + (1 - a) log (1 - p))`, and `crossEntropy_le_clip` applies. -/
theorem bernoulli_isMLE {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (μ : Measure Ω)
    (O : ℕ → Ω → Bool) :
    bernoulli.IsMLE μ (Set.Icc ε (1 - ε)) O
      (fun n ω ↦ max ε (min (1 - ε) (sampleMean successIndicator O n ω))) := by
  intro n
  refine ae_of_all _ fun ω ↦ ?_
  set k : ℝ := ∑ i ∈ Finset.range n, successIndicator (O i ω) with hk
  set q := max ε (min (1 - ε) (sampleMean successIndicator O n ω)) with hq
  have hqK : q ∈ Set.Icc ε (1 - ε) :=
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  refine ⟨hqK, fun p hp ↦ ?_⟩
  have hlogL : ∀ r ∈ Set.Icc ε (1 - ε), Real.log (bernoulli.likelihood O n ω r) =
      k * Real.log r + (n - k) * Real.log (1 - r) := by
    intro r hr
    rw [likelihood, Real.log_prod (fun i _ ↦
      (bernoulli_density_pos (Icc_subset_bernoulli_Θ hε hr) _).ne')]
    simp only [bernoulli_log_density, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hk]
  have hLpos : ∀ r ∈ Set.Icc ε (1 - ε), 0 < bernoulli.likelihood O n ω r := fun r hr ↦
    Finset.prod_pos fun i _ ↦ bernoulli_density_pos (Icc_subset_bernoulli_Θ hε hr) _
  rw [← Real.log_le_log_iff (hLpos p hp) (hLpos q hqK), hlogL p hp, hlogL q hqK]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [hk]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set a := sampleMean successIndicator O n ω with ha
  have hkeq : k = n * a := by
    rw [ha, sampleMean, hk]
    field_simp
  have hmain := crossEntropy_le_clip (a := a) hε hε2 hp
  rw [hkeq]
  have := mul_le_mul_of_nonneg_left hmain hn'.le
  nlinarith [this]

/-- **Consistency of the Bernoulli maximum likelihood estimator.** For `0 < ε` and an i.i.d.
sample with law `P_p₀`, `p₀ ∈ [ε, 1 - ε]`, every maximum likelihood estimator over `[ε, 1 - ε]`
is consistent for `p₀`. Every hypothesis of `isConsistent_of_isMLE` holds: the interval is
compact, the parameter is identified, the densities are continuous and positive on it, and
`|log f(x;p)| ≤ -log ε`. -/
theorem bernoulli_isConsistent_of_isMLE {ε : ℝ} (hε : 0 < ε) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {O : ℕ → Ω → Bool} (hO : IsIIDSample O μ) {p₀ : ℝ}
    (hp₀ : p₀ ∈ Set.Icc ε (1 - ε)) (hlaw : μ.map (O 0) = bernoulli.law p₀)
    {θh : ℕ → Ω → ℝ} (hmle : bernoulli.IsMLE μ (Set.Icc ε (1 - ε)) O θh) :
    IsConsistent θh p₀ μ := by
  have hK := Icc_subset_bernoulli_Θ hε
  have := isProbabilityMeasure_law (F := bernoulli) (hK hp₀)
  refine isConsistent_of_isMLE hO hlaw isCompact_Icc hK hp₀
    (bernoulli_pointIdentified.mono hK) (ae_of_all _ fun x ↦ ?_)
    (ae_of_all _ fun x p hp ↦ bernoulli_density_pos (hK hp) x)
    (H := fun _ ↦ -Real.log ε) (integrable_const _) (ae_of_all _ fun x p hp ↦ ?_) hmle
  · cases x
    · exact (continuous_const.sub continuous_id).continuousOn
    · exact continuous_id.continuousOn
  · have hpos := bernoulli_density_pos (hK hp) x
    have hle1 : bernoulli.density p x ≤ 1 := by
      rw [bernoulli_density]; split_ifs <;> linarith [hp.1, hp.2]
    have hεle : ε ≤ bernoulli.density p x := by
      rw [bernoulli_density]; split_ifs <;> linarith [hp.1, hp.2]
    rw [logLik, abs_of_nonpos (Real.log_nonpos hpos.le hle1)]
    exact neg_le_neg (Real.log_le_log hε hεle)

/-- **The clipped sample proportion is consistent**: for `0 < ε ≤ 1/2` and an i.i.d. sample with
law `P_p₀`, `p₀ ∈ [ε, 1 - ε]`, the sample proportion clipped to `[ε, 1 - ε]` converges to `p₀`
in probability. -/
theorem bernoulli_clip_isConsistent {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {O : ℕ → Ω → Bool} (hO : IsIIDSample O μ) {p₀ : ℝ}
    (hp₀ : p₀ ∈ Set.Icc ε (1 - ε)) (hlaw : μ.map (O 0) = bernoulli.law p₀) :
    IsConsistent (fun n ω ↦ max ε (min (1 - ε) (sampleMean successIndicator O n ω))) p₀ μ :=
  bernoulli_isConsistent_of_isMLE hε hO hp₀ hlaw (bernoulli_isMLE hε hε2 μ O)

end ParametricFamily

end CausalInference
