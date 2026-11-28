/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.BootstrapSample
public import CausalInference.Estimation.TriangularArrayLimit
public import CausalInference.Estimation.LawOfLargeNumbers
public import CausalInference.Estimation.PosteriorLimitTotalVariation

/-!
# The conditional central limit theorem of the bootstrap mean

Given the data path `ω`, the resample of size `n` consists of `n` independent draws from the
empirical law of the first `n` observations (`Bootstrap.resampleLaw`). For each `n` this is a row
of a triangular array, and the Lindeberg theorem
(`TriangularArray.tendstoInDistribution_sum`) applies along every data path on which the empirical
second moments converge and the empirical Lindeberg condition holds
(`Bootstrap.tendstoInDistribution_resample_of_path`, stated for a function `g n` that may change
with `n` and is centered along the path).

For an i.i.d. sample with a finite second moment both conditions hold almost surely: the empirical
second moments by the strong law, and the empirical Lindeberg condition
`n⁻¹ ∑_{k < n} h(O_k)² 1{ε √n < |h(O_k)|} → 0` by the strong law for the truncated squares
`h² 1{M < |h|}` and dominated convergence in `M` (`Bootstrap.ae_tendsto_lindeberg`). Hence, for
almost every data path, `√n (X̄*_n - X̄_n)` given the data converges in law to `N(0, Var f)`
(`Bootstrap.ae_tendstoInDistribution_resampleMean`). In the form used for confidence intervals:
the bootstrap law of the resample mean satisfies the weak Bernstein and von Mises predicate with
centering `X̄_n`, that is, conditional weak convergence in probability
(`Bootstrap.isBernsteinVonMisesWeak_resampleMean`); and on the product of the data space and the
index space the conditional expectation of `φ(√n (X̄*_n - X̄_n))` given the data converges almost
surely (`Bootstrap.condExp_resampleMean_tendsto`).

## Main definitions

* `Bootstrap.resampleMean f n y`: the mean `n⁻¹ ∑_i f (y i)` of a resample `y`.

## Main results

* `Bootstrap.tendstoInDistribution_resample_of_path`, `Bootstrap.ae_tendsto_lindeberg`,
  `Bootstrap.ae_tendstoInDistribution_resampleMean`,
  `Bootstrap.isBernsteinVonMisesWeak_resampleMean`, `Bootstrap.condExp_resampleMean_tendsto`.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* P. J. Bickel and D. A. Freedman (1981), *Some asymptotic theory for the bootstrap*, Annals of
  Statistics 9.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 23.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace CausalInference

namespace Bootstrap

open PosteriorLimit

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-! ### Tools -/

/-- Convergence in distribution with probability spaces that change with `n` depends only on the
tail of the sequence. -/
theorem tendstoInDistribution_congr_eventually {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {Ωn : ℕ → Type*}
    {m : ∀ n, MeasurableSpace (Ωn n)} {Pn : (n : ℕ) → Measure (Ωn n)}
    [∀ n, IsProbabilityMeasure (Pn n)] {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X X' : (n : ℕ) → Ωn n → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z Pn P') (hXX' : ∀ᶠ n in atTop, X n = X' n)
    (hm : ∀ n, AEMeasurable (X' n) (Pn n)) : TendstoInDistribution X' atTop Z Pn P' where
  forall_aemeasurable := hm
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.congr' (hXX'.mono fun n hn ↦ Subtype.ext (by simp only [hn]))

/-- Integrals of a function of one resampled observation are sample means. -/
theorem integral_comp_eval_resampleLaw {g : 𝒪 → ℝ} (hg : Measurable g) (O : ℕ → Ω → 𝒪) (n : ℕ)
    (ω : Ω) (i : Fin n) : ∫ y, g (y i) ∂resampleLaw O n ω = sampleMean g O n ω := by
  rw [← integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable,
    (hasLaw_eval_resampleLaw O n ω i).map_eq,
    integral_empiricalMeasure_of_stronglyMeasurable hg.stronglyMeasurable]

/-- A measurable function of one resampled observation is square integrable. -/
theorem memLp_comp_eval_resampleLaw {E : Type*} [NormedAddCommGroup E] {g : 𝒪 → E}
    (hg : StronglyMeasurable g) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) (i : Fin n) :
    MemLp (fun y : Fin n → 𝒪 ↦ g (y i)) 2 (resampleLaw O n ω) := by
  have h := memLp_two_empiricalMeasure hg O n ω
  rw [← (hasLaw_eval_resampleLaw O n ω i).map_eq] at h
  exact (memLp_map_measure_iff hg.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h

/-- Rescaling inside a Lindeberg term: for `n ≥ 1`,
`(n^{-1/2} a)² 1{ε < |n^{-1/2} a|} = n⁻¹ a² 1{ε √n < |a|}`. -/
theorem indicator_inv_sqrt_mul {n : ℕ} (hn : 1 ≤ n) (ε a : ℝ) :
    {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) ((√(n : ℝ))⁻¹ * a) =
      (n : ℝ)⁻¹ * {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) a := by
  have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have habs : |(√(n : ℝ))⁻¹ * a| = |a| / √(n : ℝ) := by
    rw [abs_mul, abs_inv, abs_of_pos hr, inv_mul_eq_div]
  have hiff : ε < |(√(n : ℝ))⁻¹ * a| ↔ ε * √(n : ℝ) < |a| := by rw [habs, lt_div_iff₀ hr]
  by_cases h : ε * √(n : ℝ) < |a|
  · rw [Set.indicator_of_mem (show _ ∈ {x : ℝ | ε < |x|} from hiff.2 h),
      Set.indicator_of_mem (show a ∈ {x : ℝ | ε * √(n : ℝ) < |x|} from h), mul_pow, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  · rw [Set.indicator_of_notMem (show _ ∉ {x : ℝ | ε < |x|} from fun h' ↦ h (hiff.1 h')),
      Set.indicator_of_notMem (show a ∉ {x : ℝ | ε * √(n : ℝ) < |x|} from h), mul_zero]

/-- A Lindeberg term is monotone in the absolute value: if `|a| ≤ |b|`, then
`a² 1{c < |a|} ≤ b² 1{c < |b|}`. -/
theorem indicator_sq_le_of_abs_le {a b : ℝ} (hab : |a| ≤ |b|) (c : ℝ) :
    {x : ℝ | c < |x|}.indicator (fun x ↦ x ^ 2) a ≤
      {x : ℝ | c < |x|}.indicator (fun x ↦ x ^ 2) b := by
  by_cases hc : c < |a|
  · rw [Set.indicator_of_mem (show a ∈ {x : ℝ | c < |x|} from hc),
      Set.indicator_of_mem (show b ∈ {x : ℝ | c < |x|} from hc.trans_le hab), ← sq_abs a,
      ← sq_abs b]
    exact pow_le_pow_left₀ (abs_nonneg _) hab 2
  · rw [Set.indicator_of_notMem (show a ∉ {x : ℝ | c < |x|} from hc)]
    exact Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _

/-! ### The central limit theorem along a data path -/

/-- **The bootstrap central limit theorem along a fixed data path.** Fix the data path `ω` and
measurable `g n : 𝒪 → ℝ`, eventually centered along the path (`∑_{k < n} g n (O k ω) = 0`), with
empirical second moments `n⁻¹ ∑_{k < n} g n (O k ω)² → v` and the empirical Lindeberg condition
`n⁻¹ ∑_{k < n} g n (O k ω)² 1{ε √n < |g n (O k ω)|} → 0` for every `ε > 0`. Then under resampling
from the empirical law of the path, `n^{-1/2} ∑_i g n (y i)` converges in distribution to every
`Y` with law `N(0, v)`. -/
theorem tendstoInDistribution_resample_of_path {O : ℕ → Ω → 𝒪} {ω : Ω} {g : ℕ → 𝒪 → ℝ}
    (hg : ∀ n, Measurable (g n)) (h0 : ∀ᶠ n in atTop, ∑ k ∈ range n, g n (O k ω) = 0) {v : ℝ}
    (hv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, g n (O k ω) ^ 2) atTop (𝓝 v))
    (hL : ∀ ε, 0 < ε → Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n,
      {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) (g n (O k ω))) atTop (𝓝 0))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 v.toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) (y : Fin n → 𝒪) ↦ (√(n : ℝ))⁻¹ * ∑ i, g n (y i)) atTop
      Y (fun n ↦ resampleLaw O n ω) P' := by
  classical
  set q : ℕ → Prop := fun n ↦ 1 ≤ n ∧ ∑ k ∈ range n, g n (O k ω) = 0 with hq
  have hqe : ∀ᶠ n in atTop, q n := (eventually_ge_atTop 1).and h0
  set g' : ℕ → 𝒪 → ℝ := fun n ↦ if q n then g n else 0 with hg'
  have hg'm : ∀ n, Measurable (g' n) := fun n ↦ by
    simp only [hg']
    split_ifs
    exacts [hg n, measurable_const]
  have hgq : ∀ n, q n → g' n = g n := fun n hn ↦ by simp [hg', hn]
  set X : (n : ℕ) → Fin n → (Fin n → 𝒪) → ℝ := fun n i y ↦ (√(n : ℝ))⁻¹ * g' n (y i) with hX
  have hind : ∀ n, iIndepFun (X n) (resampleLaw O n ω) := fun n ↦
    (iIndepFun_resampleLaw O n ω).comp (fun _ x ↦ (√(n : ℝ))⁻¹ * g' n x)
      fun _ ↦ (hg'm n).const_mul _
  have h2 : ∀ n i, MemLp (X n i) 2 (resampleLaw O n ω) := fun n i ↦
    (memLp_comp_eval_resampleLaw (hg'm n).stronglyMeasurable O n ω i).const_mul _
  have hmean0 : ∀ n, sampleMean (g' n) O n ω = 0 := by
    intro n
    by_cases hn : q n
    · rw [hgq n hn, sampleMean, hn.2, mul_zero]
    · simp [hg', hn, sampleMean]
  have h0' : ∀ n i, ∫ y, X n i y ∂resampleLaw O n ω = 0 := fun n i ↦ by
    simp only [hX]
    rw [integral_const_mul, integral_comp_eval_resampleLaw (hg'm n), hmean0, mul_zero]
  have hcard : ∀ n (c : ℝ), ∑ _i : Fin n, c = n * c := fun n c ↦ by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hv' : Tendsto (fun n ↦ ∑ i, ∫ y, X n i y ^ 2 ∂resampleLaw O n ω) atTop (𝓝 v) := by
    refine hv.congr' (hqe.mono fun n hn ↦ ?_)
    have hn0 : (n : ℝ) ≠ 0 := by have := hn.1; positivity
    have hpt : ∀ i, ∫ y, X n i y ^ 2 ∂resampleLaw O n ω =
        (n : ℝ)⁻¹ * sampleMean (fun z ↦ g' n z ^ 2) O n ω := by
      intro i
      have : (fun y : Fin n → 𝒪 ↦ X n i y ^ 2) = fun y ↦ (n : ℝ)⁻¹ * (g' n (y i) ^ 2) := by
        funext y
        simp only [hX]
        rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      rw [this, integral_const_mul, integral_comp_eval_resampleLaw ((hg'm n).pow_const 2)]
    simp only [hpt, hcard, sampleMean, hgq n hn]
    field_simp
  have hL' : ∀ ε, 0 < ε → Tendsto (fun n ↦ ∑ i,
      ∫ y, {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) (X n i y) ∂resampleLaw O n ω) atTop
      (𝓝 0) := by
    intro ε hε
    refine (hL ε hε).congr' (hqe.mono fun n hn ↦ ?_)
    have hn0 : (n : ℝ) ≠ 0 := by have := hn.1; positivity
    have hAm : MeasurableSet {x : ℝ | ε * √(n : ℝ) < |x|} :=
      measurableSet_lt measurable_const (by fun_prop)
    have hpt : ∀ i, ∫ y, {x : ℝ | ε < |x|}.indicator (fun x ↦ x ^ 2) (X n i y)
        ∂resampleLaw O n ω = (n : ℝ)⁻¹ * sampleMean
          (fun z ↦ {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) (g' n z)) O n ω := by
      intro i
      simp only [hX, indicator_inv_sqrt_mul hn.1]
      rw [integral_const_mul, integral_comp_eval_resampleLaw
        (g := fun z ↦ {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) (g' n z))
        (((measurable_id.pow_const 2).indicator hAm).comp (hg'm n))]
    simp only [hpt, hcard, sampleMean, hgq n hn]
    field_simp
  have hclt := TriangularArray.tendstoInDistribution_sum hind h2 h0' hv' hL' hY
  refine tendstoInDistribution_congr_eventually hclt (hqe.mono fun n hn ↦ ?_) fun n ↦ ?_
  · funext y
    simp only [hX, hgq n hn, Finset.mul_sum]
  · exact (Finset.measurable_fun_sum _ fun i _ ↦
      (hg n).comp (measurable_pi_apply i)).const_mul _ |>.aemeasurable

/-! ### The empirical Lindeberg condition along almost every path -/

/-- **The empirical Lindeberg condition holds almost surely.** For an i.i.d. sample and a
measurable `h` with `E[h(O_0)²] < ∞`, almost surely, for every `ε > 0`,
`n⁻¹ ∑_{k < n} h(O_k)² 1{ε √n < |h(O_k)|} → 0`. For each integer `M` the strong law gives
`n⁻¹ ∑_{k < n} h(O_k)² 1{M < |h(O_k)|} → E[h² 1{M < |h|}]`, which tends to `0` as `M → ∞` by
dominated convergence, and the Lindeberg average lies below it once `ε √n > M`. -/
theorem ae_tendsto_lindeberg {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O P) {h : 𝒪 → ℝ} (hm : Measurable h)
    (h2 : Integrable (fun ω ↦ h (O 0 ω) ^ 2) P) :
    ∀ᵐ ω ∂P, ∀ ε, 0 < ε → Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n,
      {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) (h (O k ω))) atTop (𝓝 0) := by
  set F : ℕ → ℝ → ℝ := fun M ↦ {x : ℝ | (M : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) with hF
  have hFm : ∀ M, Measurable (F M) := fun M ↦
    (measurable_id.pow_const 2).indicator (measurableSet_lt measurable_const (by fun_prop))
  have hFle : ∀ M x, ‖F M x‖ ≤ x ^ 2 := fun M x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)]
    exact Set.indicator_le_self' (fun _ _ ↦ sq_nonneg _) x
  have hFi : ∀ M, Integrable (fun ω ↦ F M (h (O 0 ω))) P := fun M ↦
    h2.mono (((hFm M).comp hm).comp_aemeasurable (hO.aemeasurable 0)).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hFle M _)
  have hslln : ∀ᵐ ω ∂P, ∀ M : ℕ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n,
      F M (h (O k ω))) atTop (𝓝 (P[fun ω ↦ F M (h (O 0 ω))])) :=
    ae_all_iff.2 fun M ↦ hO.tendsto_ae_smul_sum (f := fun z ↦ F M (h z)) ((hFm M).comp hm) (hFi M)
  have hdct : Tendsto (fun M : ℕ ↦ P[fun ω ↦ F M (h (O 0 ω))]) atTop (𝓝 0) := by
    have hlim := tendsto_integral_of_dominated_convergence (f := fun _ ↦ (0 : ℝ))
      (fun ω ↦ h (O 0 ω) ^ 2) (fun M ↦ (hFi M).aestronglyMeasurable) h2
      (fun M ↦ ae_of_all _ fun ω ↦ hFle M _)
      (ae_of_all _ fun ω ↦ by
        obtain ⟨N, hN⟩ := exists_nat_ge |h (O 0 ω)|
        refine tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun M hM ↦ ?_)
        have hz : ¬ (M : ℝ) < |h (O 0 ω)| := not_lt.2 (hN.trans (by exact_mod_cast hM))
        exact (Set.indicator_of_notMem hz _).symm)
    rwa [integral_zero] at hlim
  filter_upwards [hslln] with ω hω ε hε
  have hsq : Tendsto (fun n : ℕ ↦ ε * √(n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ)⁻¹ * ∑ k ∈ range n,
      {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) (h (O k ω)) := fun n ↦
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))
      (Finset.sum_nonneg fun k _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)
  refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun n ↦ ha.trans_le (hnn n),
    fun δ hδ ↦ ?_⟩
  obtain ⟨M, hM⟩ := (hdct.eventually (gt_mem_nhds hδ)).exists
  filter_upwards [(hω M).eventually (gt_mem_nhds hM), hsq.eventually_gt_atTop (M : ℝ)]
    with n hn hMn
  refine lt_of_le_of_lt ?_ hn
  rw [smul_eq_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ ?_)
    (inv_nonneg.2 (Nat.cast_nonneg n))
  exact Set.indicator_le_indicator_of_subset (fun z hz ↦ hMn.trans hz)
    (fun _ ↦ sq_nonneg _) _

/-! ### The bootstrap of the mean -/

/-- The mean `n⁻¹ ∑_i f (y i)` of a resample `y` of size `n`. -/
noncomputable def resampleMean (f : 𝒪 → ℝ) (n : ℕ) (y : Fin n → 𝒪) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (y i)

theorem measurable_resampleMean {f : 𝒪 → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (resampleMean f n) :=
  (Finset.measurable_fun_sum _ fun i _ ↦ hf.comp (measurable_pi_apply i)).const_mul _

omit [MeasurableSpace 𝒪] in
/-- The sample mean of the data is the mean of the data prefix. -/
theorem sampleMean_eq_resampleMean_dataPrefix (f : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    sampleMean f O n ω = resampleMean f n (dataPrefix O n ω) := by
  simp [sampleMean, resampleMean, dataPrefix, Finset.sum_range]

omit [MeasurableSpace 𝒪] in
/-- The rescaled bootstrap mean as a normalized centered sum, for every `n`:
`√n (n⁻¹ ∑_i f(y_i) - m) = n^{-1/2} ∑_i (f(y_i) - m)`. -/
theorem sqrt_mul_resampleMean_sub (f : 𝒪 → ℝ) (n : ℕ) (y : Fin n → 𝒪) (m : ℝ) :
    √(n : ℝ) * (resampleMean f n y - m) = (√(n : ℝ))⁻¹ * ∑ i, (f (y i) - m) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnr : (n : ℝ) = √(n : ℝ) * √(n : ℝ) := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    resampleMean]
  set r := √(n : ℝ)
  rw [hnr]
  field_simp

/-- **The conditional central limit theorem of the bootstrap mean.** Let `O` be an i.i.d. sample
and `f` measurable with `E[f(O_0)²] < ∞`. For almost every data path `ω`, under resampling from
the empirical law of the first `n` observations, `√n (X̄*_n - X̄_n)` converges in distribution to
`N(0, Var f(O_0))`, where `X̄*_n` is the resample mean of `f` and `X̄_n` the sample mean. -/
theorem ae_tendstoInDistribution_resampleMean {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O P) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 P) :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) (y : Fin n → 𝒪) ↦ √(n : ℝ) * (resampleMean f n y - sampleMean f O n ω))
      atTop (fun x ↦ x) (fun n ↦ resampleLaw O n ω)
      (gaussianReal 0 (Var[fun ω ↦ f (O 0 ω); P]).toNNReal) := by
  set m := P[fun ω ↦ f (O 0 ω)] with hm
  set s2 := P[fun ω ↦ f (O 0 ω) ^ 2] with hs2
  set C := |m| + 1 with hC
  set h : 𝒪 → ℝ := fun z ↦ |f z| + C with hh
  have hhm : Measurable h := by simp only [hh]; fun_prop
  have hh2 : Integrable (fun ω ↦ h (O 0 ω) ^ 2) P := by
    have h1 := (hf2.norm.add (memLp_const (μ := P) C))
    simp only [Real.norm_eq_abs] at h1
    exact h1.integrable_sq
  have hvar : Var[fun ω ↦ f (O 0 ω); P] = s2 - m ^ 2 := by
    rw [variance_eq_sub hf2]
    rfl
  have hmean := hO.tendsto_ae_smul_sum hf (hf2.integrable one_le_two)
  have hsq := hO.tendsto_ae_smul_sum (hf.pow_const 2) hf2.integrable_sq
  filter_upwards [hmean, hsq, ae_tendsto_lindeberg hO hhm hh2] with ω hω1 hω2 hω3
  simp only [smul_eq_mul] at hω1 hω2
  set xb : ℕ → ℝ := fun n ↦ sampleMean f O n ω with hxb
  have hxb' : Tendsto xb atTop (𝓝 m) := hω1
  have hsum : ∀ n : ℕ, 1 ≤ n → ∑ k ∈ range n, f (O k ω) = n * xb n := fun n hn ↦ by
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [hxb, sampleMean]
    field_simp
  set g : ℕ → 𝒪 → ℝ := fun n z ↦ f z - xb n with hg
  have hgm : ∀ n, Measurable (g n) := fun n ↦ hf.sub_const _
  have h0 : ∀ᶠ n in atTop, ∑ k ∈ range n, g n (O k ω) = 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      hsum n hn, sub_self]
  have hv : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n, g n (O k ω) ^ 2) atTop
      (𝓝 (s2 - m ^ 2)) := by
    refine (hω2.sub (hxb'.pow 2)).congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hk : ∀ k, g n (O k ω) ^ 2 = f (O k ω) ^ 2 - 2 * xb n * f (O k ω) + xb n ^ 2 :=
      fun k ↦ by simp only [hg]; ring
    have e : ∑ k ∈ range n, g n (O k ω) ^ 2 =
        ∑ k ∈ range n, f (O k ω) ^ 2 - 2 * xb n * ∑ k ∈ range n, f (O k ω) + n * xb n ^ 2 := by
      simp only [hk, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    beta_reduce
    rw [e, hsum n hn]
    field_simp
    ring
  have hL : ∀ ε, 0 < ε → Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ k ∈ range n,
      {x : ℝ | ε * √(n : ℝ) < |x|}.indicator (fun x ↦ x ^ 2) (g n (O k ω))) atTop (𝓝 0) := by
    intro ε hε
    have hclose : ∀ᶠ n in atTop, |xb n| ≤ C := by
      filter_upwards [hxb'.eventually (Metric.ball_mem_nhds m one_pos)] with n hn
      rw [Real.dist_eq] at hn
      have := abs_sub_abs_le_abs_sub (xb n) m
      simp only [hC]
      linarith
    refine squeeze_zero' (Eventually.of_forall fun n ↦ mul_nonneg
      (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun k _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _))
      (hclose.mono fun n hn ↦ ?_) (hω3 ε hε)
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ ?_)
      (inv_nonneg.2 (Nat.cast_nonneg _))
    refine indicator_sq_le_of_abs_le ?_ _
    have hC0 : 0 ≤ C := by positivity
    simp only [hg, hh]
    rw [abs_of_nonneg (by positivity : 0 ≤ |f (O k ω)| + C)]
    exact (abs_sub _ _).trans (by linarith)
  have hY : HasLaw (fun x : ℝ ↦ x) (gaussianReal 0 (s2 - m ^ 2).toNNReal)
      (gaussianReal 0 (s2 - m ^ 2).toNNReal) := ⟨aemeasurable_id, Measure.map_id⟩
  have hpath := tendstoInDistribution_resample_of_path hgm h0 hv hL hY
  rw [hvar]
  refine tendstoInDistribution_congr_eventually hpath (Eventually.of_forall fun n ↦ ?_)
    fun n ↦ (((measurable_resampleMean hf n).sub_const _).const_mul _).aemeasurable
  funext y
  rw [sqrt_mul_resampleMean_sub]

/-- **Conditional weak convergence in probability of the bootstrap mean.** Under the hypotheses of
`Bootstrap.ae_tendstoInDistribution_resampleMean`, the bootstrap laws of the resample mean,
centered at the sample mean and rescaled by `√n`, converge weakly to `N(0, Var f(O_0))` in
probability: for every bounded continuous `φ`,
`∫ φ(√n (x - X̄_n)) d(bootstrap law)(x) → ∫ φ dN(0, Var f)` in probability. This is the weak
Bernstein and von Mises predicate for the bootstrap laws. -/
theorem isBernsteinVonMisesWeak_resampleMean {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O P) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 P) :
    IsBernsteinVonMisesWeak P (bootstrapLaw (resampleMean f) O) (sampleMean f O)
      (gaussianReal 0 (Var[fun ω ↦ f (O 0 ω); P]).toNNReal) where
  isProbabilityMeasure _ _ := inferInstance
  isProbabilityMeasure_limit := inferInstance
  tendsto φ hφc hφb := by
    obtain ⟨C, hC⟩ := hφb
    set N := gaussianReal 0 (Var[fun ω ↦ f (O 0 ω); P]).toNNReal with hN
    have hrw : ∀ (n : ℕ) ω, ∫ θ, φ (√(n : ℝ) • (θ - sampleMean f O n ω))
        ∂bootstrapLaw (resampleMean f) O n ω =
        ∫ y, φ (√(n : ℝ) * (resampleMean f n y - resampleMean f n (dataPrefix O n ω)))
          ∂resampleLaw O n ω := by
      intro n ω
      rw [bootstrapLaw, integral_map (measurable_resampleMean hf n).aemeasurable
        (f := fun θ ↦ φ (√(n : ℝ) • (θ - sampleMean f O n ω)))
        (hφc.comp (by fun_prop : Continuous fun θ : ℝ ↦
          √(n : ℝ) • (θ - sampleMean f O n ω))).aestronglyMeasurable,
        sampleMean_eq_resampleMean_dataPrefix]
      simp only [smul_eq_mul]
    simp only [hrw]
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun ω ↦ ∫ y,
        φ (√(n : ℝ) * (resampleMean f n y - resampleMean f n (dataPrefix O n ω)))
          ∂resampleLaw O n ω) P := fun n ↦
      aestronglyMeasurable_integral_resampleLaw (fun k ↦ hO.aemeasurable k) n
        (H := fun x y ↦ φ (√(n : ℝ) * (resampleMean f n y - resampleMean f n x)))
        (hφc.measurable.comp ((((measurable_resampleMean hf n).comp measurable_snd).sub
          ((measurable_resampleMean hf n).comp measurable_fst)).const_mul _)).stronglyMeasurable
    refine tendstoInMeasure_of_tendsto_ae hmeas ?_
    filter_upwards [ae_tendstoInDistribution_resampleMean hO hf hf2] with ω hω
    set b : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨φ, hφc⟩ (2 * C) fun x y ↦ by
      rw [Real.dist_eq]
      have := hC x
      have := hC y
      simp only [ContinuousMap.coe_mk]
      rw [abs_le] at *
      constructor <;> linarith [abs_le.1 (hC x), abs_le.1 (hC y)]
    have h1 := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hω.forall_aemeasurable aemeasurable_id).1 hω b
    simp only [b, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk, id_eq] at h1
    refine h1.congr fun n ↦ ?_
    rw [← sampleMean_eq_resampleMean_dataPrefix]

/-- **The conditional expectation on the product space.** For measurable i.i.d. data, `f` with
`E[f(O_0)²] < ∞` and a bounded continuous `φ`, the conditional expectation of
`φ(√n (X̄*_n - X̄_n))` given the data, under `P ⊗ resampleIndexLaw n`, has a version
`ω ↦ ∫ φ(√n (X̄*_n - X̄_n)) d(resample law at ω)` that converges to `∫ φ dN(0, Var f)` for
almost every data point. -/
theorem condExp_resampleMean_tendsto {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O P) (hOm : ∀ k, Measurable (O k)) {f : 𝒪 → ℝ}
    (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 P) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφb : ∃ C, ∀ x, |φ x| ≤ C) :
    (∀ n : ℕ, (P.prod (resampleIndexLaw n))[fun p ↦
        φ (√(n : ℝ) * (resampleMean f n (resample O n p.1 p.2) - sampleMean f O n p.1)) |
        MeasurableSpace.comap Prod.fst mΩ] =ᵐ[P.prod (resampleIndexLaw n)]
      fun p ↦ ∫ y, φ (√(n : ℝ) * (resampleMean f n y - sampleMean f O n p.1))
        ∂resampleLaw O n p.1) ∧
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ∫ y, φ (√(n : ℝ) * (resampleMean f n y - sampleMean f O n ω))
        ∂resampleLaw O n ω) atTop
      (𝓝 (∫ x, φ x ∂gaussianReal 0 (Var[fun ω ↦ f (O 0 ω); P]).toNNReal)) := by
  obtain ⟨C, hC⟩ := hφb
  refine ⟨fun n ↦ ?_, ?_⟩
  · have h := condExp_bootstrapStat_ae_eq P hOm n
      (T := fun x y ↦ √(n : ℝ) * (resampleMean f n y - resampleMean f n x))
      ((((measurable_resampleMean hf n).comp measurable_snd).sub
        ((measurable_resampleMean hf n).comp measurable_fst)).const_mul _) hφc.measurable ⟨C, hC⟩
    simpa only [← sampleMean_eq_resampleMean_dataPrefix] using h
  · filter_upwards [ae_tendstoInDistribution_resampleMean hO hf hf2] with ω hω
    set b : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨φ, hφc⟩ (2 * C) fun x y ↦ by
      rw [Real.dist_eq]
      simp only [ContinuousMap.coe_mk]
      rw [abs_le]
      constructor <;> linarith [abs_le.1 (hC x), abs_le.1 (hC y)]
    have h1 := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hω.forall_aemeasurable aemeasurable_id).1 hω b
    simpa only [b, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk, id_eq] using h1

end Bootstrap

end CausalInference
