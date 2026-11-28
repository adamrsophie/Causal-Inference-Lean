/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitQuantile
public import CausalInference.Estimation.DeltaMethod
public import CausalInference.Estimation.LawOfLargeNumbers
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Monte Carlo approximation from i.i.d. draws

Draws `D₀, D₁, ...` are i.i.d. under `P` with law `μ = P.map D₀`, for instance draws from a fixed
posterior law. The empirical law of the first `M` draws is `empiricalMeasure D M ω`.

* `tendsto_ae_empiricalMeasure_real`: for every measurable set `A`, almost surely
  `μ̂_M(A) → μ(A)` (strong law).
* `tendsto_ae_empiricalMeasure`: on `ℝ`, almost surely the empirical laws converge **weakly** to
  `μ` (as probability measures, in the topology of weak convergence). The proof runs the strong
  law simultaneously over the countable family of finite unions of open intervals with rational
  endpoints and then applies the open set form of the portmanteau theorem.
* `tendsto_ae_quantile_empiricalMeasure`: if the distribution function of `μ` crosses the level
  `p` strictly at `c` (`F(c - ε) < p < F(c + ε)` for all `ε > 0`), then almost surely the
  empirical `p` quantile converges to `c`. This is exactly the condition the proof uses; it
  forces `p ∈ (0, 1)` and `c = q_μ(p)`. Without it the empirical quantile may oscillate.
* `sqrt_mul_integral_empiricalMeasure_sub_boundedInProbability`: for `f` with
  `E f(D₀)² < ∞`, the Monte Carlo error `∫ f dμ̂_M - ∫ f dμ` is `O_p(M^{-1/2})`:
  `√M (∫ f dμ̂_M - ∫ f dμ)` is bounded in probability.
* `ae_data_tendsto_ae_empiricalMeasure`, `ae_data_tendsto_ae_quantile_empiricalMeasure`,
  `ae_data_sqrt_mul_integral_empiricalMeasure_sub_boundedInProbability`: the same statements
  for a family of posterior laws `Q x` indexed by the data, holding for almost every data value.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped ENNReal NNReal

namespace CausalInference

namespace EmpiricalLaw

open BiasAnalysis.Distributions

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {P : Measure Ω}

/-- The empirical mass of a measurable set is the sample mean of its indicator. -/
lemma empiricalMeasure_real_apply [MeasurableSingletonClass 𝒪] (D : ℕ → Ω → 𝒪) {A : Set 𝒪}
    (hA : MeasurableSet A) (n : ℕ) (ω : Ω) :
    (empiricalMeasure D n ω).real A = sampleMean (A.indicator 1) D n ω := by
  rw [← integral_empiricalMeasure, integral_indicator_one hA]

/-- **The strong law for the empirical law.** For i.i.d. draws with law `μ = P.map D₀` and a
measurable set `A`, almost surely `μ̂_M(A) → μ(A)`. -/
theorem tendsto_ae_empiricalMeasure_real [IsProbabilityMeasure P] [MeasurableSingletonClass 𝒪]
    {D : ℕ → Ω → 𝒪} (hD : IsIIDSample D P) {A : Set 𝒪} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (empiricalMeasure D n ω).real A) atTop
      (𝓝 ((P.map (D 0)).real A)) := by
  have h0 : AEMeasurable (D 0) P := (hD.ident 0).aemeasurable_fst
  have hm : Measurable (A.indicator (1 : 𝒪 → ℝ)) := measurable_const.indicator hA
  have hint : Integrable (fun ω ↦ A.indicator (1 : 𝒪 → ℝ) (D 0 ω)) P := by
    refine (integrable_const (1 : ℝ)).mono' (hm.comp_aemeasurable h0).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    by_cases hx : D 0 ω ∈ A <;> simp [Set.indicator, hx]
  have hval : P[fun ω ↦ A.indicator (1 : 𝒪 → ℝ) (D 0 ω)] = (P.map (D 0)).real A := by
    rw [← integral_map h0 hm.aestronglyMeasurable, integral_indicator_one hA]
  filter_upwards [hD.tendsto_ae_smul_sum hm hint] with ω hω
  rw [hval] at hω
  refine hω.congr fun n ↦ ?_
  rw [empiricalMeasure_real_apply D hA, sampleMean, smul_eq_mul]

/-- Finite unions of open intervals with rational endpoints. -/
def ratIntervalUnion (T : Finset (ℚ × ℚ)) : Set ℝ := ⋃ q ∈ T, Ioo (q.1 : ℝ) q.2

lemma measurableSet_ratIntervalUnion (T : Finset (ℚ × ℚ)) :
    MeasurableSet (ratIntervalUnion T) :=
  Finset.measurableSet_biUnion _ fun _ _ ↦ measurableSet_Ioo

/-- Every open subset of `ℝ` is the union of the finite unions of rational open intervals it
contains, a family that is monotone in the finite index set. -/
lemma iUnion_ratIntervalUnion_filter {G : Set ℝ} (hG : IsOpen G) :
    open Classical in
    ⋃ T : Finset (ℚ × ℚ), ratIntervalUnion (T.filter fun q ↦ Ioo (q.1 : ℝ) q.2 ⊆ G) = G := by
  classical
  refine Subset.antisymm (iUnion_subset fun T ↦ iUnion₂_subset fun q hq ↦ ?_) fun x hx ↦ ?_
  · exact (Finset.mem_filter.1 hq).2
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hG x hx
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x - ε < x by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    have hsub : Ioo (a : ℝ) b ⊆ G := fun y hy ↦ hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2])
    refine mem_iUnion.2 ⟨{(a, b)}, mem_iUnion₂.2 ⟨(a, b), ?_, ha2, hb1⟩⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_singleton_self _, hsub⟩

/-- **Almost sure weak convergence of the empirical law on `ℝ`.** For i.i.d. real draws with law
`μ = P.map D₀`, almost surely the empirical laws `μ̂_{M+1}` of the first `M + 1` draws converge
to `μ` in the topology of weak convergence of probability measures. -/
theorem tendsto_ae_empiricalMeasure [IsProbabilityMeasure P] {D : ℕ → Ω → ℝ}
    (hD : IsIIDSample D P) :
    ∀ᵐ ω ∂P, Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ ↦
        (⟨empiricalMeasure D (n + 1) ω, inferInstance⟩ : ProbabilityMeasure ℝ)) atTop
      (𝓝 (⟨P.map (D 0), (Measure.isProbabilityMeasure_map_iff
        (hD.ident 0).aemeasurable_fst).2 inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  classical
  have hall : ∀ᵐ ω ∂P, ∀ T : Finset (ℚ × ℚ),
      Tendsto (fun n ↦ (empiricalMeasure D n ω).real (ratIntervalUnion T)) atTop
        (𝓝 ((P.map (D 0)).real (ratIntervalUnion T))) :=
    ae_all_iff.2 fun T ↦ tendsto_ae_empiricalMeasure_real hD (measurableSet_ratIntervalUnion T)
  have : IsProbabilityMeasure (P.map (D 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hD.ident 0).aemeasurable_fst).2 inferInstance
  filter_upwards [hall] with ω hω
  refine tendsto_of_forall_isOpen_le_liminf_nat' fun G hG ↦ ?_
  simp only [ProbabilityMeasure.coe_mk]
  set s : Finset (ℚ × ℚ) → Set ℝ :=
    fun T ↦ ratIntervalUnion (T.filter fun q ↦ Ioo (q.1 : ℝ) q.2 ⊆ G) with hs
  have hmono : Monotone s := fun T T' hT ↦ iUnion₂_subset fun q hq ↦
    subset_iUnion₂ (s := fun q _ ↦ Ioo (q.1 : ℝ) q.2) q (Finset.filter_subset_filter _ hT hq)
  have hsub : ∀ T, s T ⊆ G := fun T ↦ iUnion₂_subset fun q hq ↦ (Finset.mem_filter.1 hq).2
  have hG' := iUnion_ratIntervalUnion_filter hG
  calc P.map (D 0) G = P.map (D 0) (⋃ T, s T) := by rw [hG']
    _ = ⨆ T, P.map (D 0) (s T) := hmono.measure_iUnion
    _ ≤ _ := iSup_le fun T ↦ ?_
  have hT : Tendsto (fun n : ℕ ↦ empiricalMeasure D (n + 1) ω (s T)) atTop
      (𝓝 (P.map (D 0) (s T))) := by
    have h1 := (ENNReal.tendsto_ofReal
      ((hω (T.filter fun q ↦ Ioo (q.1 : ℝ) q.2 ⊆ G)).comp (tendsto_add_atTop_nat 1)))
    rw [ofReal_measureReal (measure_ne_top _ _)] at h1
    refine h1.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    exact ofReal_measureReal (measure_ne_top _ _)
  rw [← hT.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n ↦ measure_mono (hsub T))

/-- **Almost sure consistency of the Monte Carlo quantile.** For i.i.d. real draws with law
`μ = P.map D₀`, if the distribution function of `μ` crosses the level `p` strictly at `c`,
`F(c - ε) < p < F(c + ε)` for every `ε > 0`, then almost surely the empirical `p` quantile of
the first `M` draws converges to `c`. -/
theorem tendsto_ae_quantile_empiricalMeasure [IsProbabilityMeasure P] {D : ℕ → Ω → ℝ}
    (hD : IsIIDSample D P) {p c : ℝ}
    (hlo : ∀ ε, 0 < ε → cdf (P.map (D 0)) (c - ε) < p)
    (hhi : ∀ ε, 0 < ε → p < cdf (P.map (D 0)) (c + ε)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ quantile (empiricalMeasure D n ω) p) atTop (𝓝 c) := by
  have : IsProbabilityMeasure (P.map (D 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hD.ident 0).aemeasurable_fst).2 inferInstance
  have hp := PosteriorLimit.mem_Ioo_of_strict_crossing hlo hhi
  set e : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with he
  have hepos : ∀ k, 0 < e k := fun k ↦ by simp only [he]; positivity
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Tendsto (fun n ↦ (empiricalMeasure D n ω).real (Iic (c - e k))) atTop
          (𝓝 ((P.map (D 0)).real (Iic (c - e k)))) ∧
        Tendsto (fun n ↦ (empiricalMeasure D n ω).real (Iic (c + e k))) atTop
          (𝓝 ((P.map (D 0)).real (Iic (c + e k)))) :=
    ae_all_iff.2 fun k ↦ (tendsto_ae_empiricalMeasure_real hD measurableSet_Iic).and
      (tendsto_ae_empiricalMeasure_real hD measurableSet_Iic)
  filter_upwards [hall] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  have hek : e k < ε := hk
  obtain ⟨h1, h2⟩ := hω k
  rw [← cdf_eq_real] at h1 h2
  have ev1 := (tendsto_order.1 h1).2 p (hlo _ (hepos k))
  have ev2 := (tendsto_order.1 h2).1 p (hhi _ (hepos k))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ev1.and (ev2.and (eventually_ge_atTop 1)))
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨a1, a2, a3⟩ := hN n hn
  have : NeZero n := ⟨by omega⟩
  rw [← cdf_eq_real] at a1 a2
  have hup : quantile (empiricalMeasure D n ω) p ≤ c + e k := (quantile_le_iff hp _).2 a2.le
  have hdown : c - e k < quantile (empiricalMeasure D n ω) p := by
    by_contra hcon
    have := (quantile_le_iff hp _).1 (not_lt.1 hcon)
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **The Monte Carlo mean error is `O_p(M^{-1/2})`.** For i.i.d. draws with law `μ = P.map D₀`
and a measurable `f` with `E f(D₀)² < ∞`, the scaled error `√M (∫ f dμ̂_M - ∫ f dμ)` is bounded
in probability. -/
theorem sqrt_mul_integral_empiricalMeasure_sub_boundedInProbability [IsProbabilityMeasure P]
    [MeasurableSingletonClass 𝒪] {D : ℕ → Ω → 𝒪} (hD : IsIIDSample D P) {f : 𝒪 → ℝ}
    (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (D 0 ω)) 2 P) :
    BoundedInProbability P
      (fun M ω ↦ √(M : ℝ) * (∫ x, f x ∂empiricalMeasure D M ω - ∫ x, f x ∂P.map (D 0))) := by
  have h0 : AEMeasurable (D 0) P := (hD.ident 0).aemeasurable_fst
  have hb := (sampleMean_isAsymptoticallyLinear hf hf2).sqrt_mul_sub_boundedInProbability hD
  rw [← integral_map h0 hf.aestronglyMeasurable] at hb
  intro η hη
  obtain ⟨C, hC, hev⟩ := hb η hη
  refine ⟨C, hC, hev.mono fun M hM ↦ ?_⟩
  simpa only [integral_empiricalMeasure] using hM

/-! ### For almost every data value -/

section Data

variable {𝒳 : Type*} {m𝒳 : MeasurableSpace 𝒳} {ρ : Measure 𝒳}

/-- **Weak convergence for almost every data value.** If for `ρ` almost every data value `x` the
draws `D x` are i.i.d. under `P` with law the posterior `Q x`, then for `ρ` almost every `x`,
almost surely the empirical laws converge weakly to `Q x`. -/
theorem ae_data_tendsto_ae_empiricalMeasure [IsProbabilityMeasure P] {Q : 𝒳 → Measure ℝ}
    [∀ x, IsProbabilityMeasure (Q x)] {D : 𝒳 → ℕ → Ω → ℝ}
    (hD : ∀ᵐ x ∂ρ, IsIIDSample (D x) P ∧ P.map (D x 0) = Q x) :
    ∀ᵐ x ∂ρ, ∀ᵐ ω ∂P, Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ ↦
        (⟨empiricalMeasure (D x) (n + 1) ω, inferInstance⟩ : ProbabilityMeasure ℝ)) atTop
      (𝓝 (⟨Q x, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  filter_upwards [hD] with x ⟨hx, hQ⟩
  have := tendsto_ae_empiricalMeasure hx
  have hQ' : (⟨Q x, inferInstance⟩ : ProbabilityMeasure ℝ) =
      ⟨P.map (D x 0), (Measure.isProbabilityMeasure_map_iff
        (hx.ident 0).aemeasurable_fst).2 inferInstance⟩ := Subtype.ext hQ.symm
  rw [hQ']
  exact this

/-- **Quantile consistency for almost every data value**, under the strict crossing condition
for the posterior `Q x` at `c x`. -/
theorem ae_data_tendsto_ae_quantile_empiricalMeasure [IsProbabilityMeasure P]
    {Q : 𝒳 → Measure ℝ} {D : 𝒳 → ℕ → Ω → ℝ}
    (hD : ∀ᵐ x ∂ρ, IsIIDSample (D x) P ∧ P.map (D x 0) = Q x) {p : ℝ} {c : 𝒳 → ℝ}
    (hlo : ∀ᵐ x ∂ρ, ∀ ε, 0 < ε → cdf (Q x) (c x - ε) < p)
    (hhi : ∀ᵐ x ∂ρ, ∀ ε, 0 < ε → p < cdf (Q x) (c x + ε)) :
    ∀ᵐ x ∂ρ, ∀ᵐ ω ∂P, Tendsto (fun n ↦ quantile (empiricalMeasure (D x) n ω) p) atTop
      (𝓝 (c x)) := by
  filter_upwards [hD, hlo, hhi] with x ⟨hx, hQ⟩ h1 h2
  rw [← hQ] at h1 h2
  exact tendsto_ae_quantile_empiricalMeasure hx h1 h2

/-- **The Monte Carlo mean rate for almost every data value.** -/
theorem ae_data_sqrt_mul_integral_empiricalMeasure_sub_boundedInProbability
    [IsProbabilityMeasure P] [MeasurableSingletonClass 𝒪] {Q : 𝒳 → Measure 𝒪}
    {D : 𝒳 → ℕ → Ω → 𝒪} (hD : ∀ᵐ x ∂ρ, IsIIDSample (D x) P ∧ P.map (D x 0) = Q x)
    {f : 𝒪 → ℝ} (hf : Measurable f) (hf2 : ∀ᵐ x ∂ρ, MemLp (fun ω ↦ f (D x 0 ω)) 2 P) :
    ∀ᵐ x ∂ρ, BoundedInProbability P
      (fun M ω ↦ √(M : ℝ) * (∫ y, f y ∂empiricalMeasure (D x) M ω - ∫ y, f y ∂Q x)) := by
  filter_upwards [hD, hf2] with x ⟨hx, hQ⟩ h2
  rw [← hQ]
  exact sqrt_mul_integral_empiricalMeasure_sub_boundedInProbability hx hf h2

end Data

end EmpiricalLaw

end CausalInference
