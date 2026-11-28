/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ExchangeableConditional
public import CausalInference.MetaAnalysis.ConjugateBetaBinomial
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import CausalInference.NetworkMetaAnalysis.AggregationLimits

/-!
# Examples of exchangeable binary sequences

* **The Bernoulli kernel** (`bernoulliClampKernel_eq_bernoulliLaw`): on `[0, 1]` it is the
  library's binary law `bernoulliLaw`.
* **The urn with one ball of each kind** (`choose_mul_urnLaw_pattern`): the urn representation
  `C(2, 1) · P(X = (1, 0)) = P(S₂ = 1) = 1` for the library's `urnLaw`.
* **A constant sequence** (`constSeq`): on `Bool` with any law `p`, the sequence
  `X₀ = X₁ = … = ω`. It is infinitely exchangeable (`infExchangeable_constSeq`), its frequency
  is `ω` read as `0/1` from `N = 1` on, and its mixing law is the law of that value, a law on
  the two points `{0, 1}` (`constSeq_mixingLaw_eq`).
* **The Beta mixture** (`betaSeq`): `Θ ~ Beta(α, β)` and, independently, i.i.d. uniform
  `U₀, U₁, …` on `[0, 1]`; `Xᵢ = 1{Uᵢ < Θ}`. Given `Θ = θ` the `Xᵢ` are i.i.d. Bernoulli(`θ`).
  The pattern probabilities are the beta binomial ones,
  `P(X₀ = x₀, …, X_{n-1} = x_{n-1}) = B(α + s, β + n - s) / B(α, β)`
  (`betaSeq_measure_pattern`); the sequence is infinitely exchangeable
  (`infExchangeable_betaSeq`), its mixing law is `Beta(α, β)` (`betaSeq_mixingLaw_eq`), the
  almost sure limit of its frequencies has the law `Beta(α, β)` (`map_limit_betaSeq`), and given
  the limit the variables are i.i.d. Bernoulli (`condDistrib_betaSeq`).

## Main definitions

* `constSeq`, `betaSeqLaw`, `betaSeq`.

## Main results

* `bernoulliClampKernel_eq_bernoulliLaw`, `choose_mul_urnLaw_pattern`,
  `infExchangeable_constSeq`, `constSeq_mixingLaw_eq`,
  `lintegral_bernstein_betaMeasure`, `betaSeq_measure_pattern`, `infExchangeable_betaSeq`,
  `betaSeq_mixingLaw_eq`, `map_limit_betaSeq`, `condDistrib_betaSeq`.

## References

* B. de Finetti, *La prévision : ses lois logiques, ses sources subjectives*, Annales de
  l'Institut Henri Poincaré 7 (1937).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Filter Topology Set BiasAnalysis.Bayesian
open scoped ENNReal unitInterval

/-! ### The Bernoulli kernel and the library's binary law -/

/-- **On `[0, 1]` the clamped Bernoulli kernel is the library's binary law**:
`bernoulliClampKernel θ = bernoulliLaw θ` for `θ ∈ [0, 1]`. -/
theorem bernoulliClampKernel_eq_bernoulliLaw {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    bernoulliClampKernel θ = NetworkMetaAnalysis.bernoulliLaw θ := by
  refine Measure.ext_iff_singleton.2 fun b => ?_
  rw [bernoulliClampKernel_singleton hθ, NetworkMetaAnalysis.bernoulliLaw,
    EffectMeasure.stratumLaw]
  cases b <;> simp [Measure.dirac_apply']

/-! ### The urn -/

/-- **The urn representation for the urn with one ball of each kind**:
`C(2, 1) · P(X = (1, 0)) = P(S₂ = 1) = 1`. -/
theorem choose_mul_urnLaw_pattern :
    ((2 : ℕ).choose (boolCount (![true, false] : Fin 2 → Bool)) : ℝ≥0∞) *
        urnLaw {ω | ∀ j, ω j = (![true, false] : Fin 2 → Bool) j} =
      urnLaw {ω | boolCount (fun j => ω j) = boolCount (![true, false] : Fin 2 → Bool)} ∧
    urnLaw {ω | boolCount (fun j => ω j) = boolCount (![true, false] : Fin 2 → Bool)} = 1 := by
  refine ⟨urnLaw_exchangeable.choose_mul_measure_pattern (fun i => measurable_pi_apply i) _, ?_⟩
  have h1 : boolCount (![true, false] : Fin 2 → Bool) = 1 := by decide
  rw [h1]
  have hm : MeasurableSet {ω : Fin 2 → Bool | boolCount (fun j => ω j) = 1} :=
    (Set.toFinite _).measurableSet
  have m1 : (![true, false] : Fin 2 → Bool) ∈
      {ω : Fin 2 → Bool | boolCount (fun j => ω j) = 1} := by
    rw [Set.mem_ofPred_eq]
    decide
  have m2 : (![false, true] : Fin 2 → Bool) ∈
      {ω : Fin 2 → Bool | boolCount (fun j => ω j) = 1} := by
    rw [Set.mem_ofPred_eq]
    decide
  simp only [urnLaw, smul_apply, add_apply, smul_eq_mul, Measure.dirac_apply' _ hm,
    Set.indicator_of_mem m1, Set.indicator_of_mem m2, Pi.one_apply]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-! ### A constant sequence -/

/-- The **constant sequence** on `Bool`: every variable is the outcome `ω`. -/
def constSeq : ℕ → Bool → Bool := fun _ ω => ω

theorem infExchangeable_constSeq (p : Measure Bool) : InfExchangeable constSeq p :=
  fun _ _ => rfl

theorem successFreq_constSeq {N : ℕ} (hN : 0 < N) (ω : Bool) :
    successFreq constSeq N ω = (ω.toNat : ℝ) := by
  rw [successFreq_eq_sum_fin]
  simp only [constSeq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The mixing law of a constant sequence** is the law of its value read as `0/1`: a law on
the two points `{0, 1}`. Every probability measure on `[0, 1]` representing the pattern
probabilities of the constant sequence is `p ∘ (ω ↦ ω.toNat)⁻¹`. -/
theorem constSeq_mixingLaw_eq (p : Measure Bool) [IsProbabilityMeasure p] {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμs : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hμr : ∀ (n : ℕ) (x : Fin n → Bool), p {ω | ∀ i : Fin n, constSeq i ω = x i} =
      ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂μ) :
    μ = p.map fun ω => (ω.toNat : ℝ) := by
  refine ((infExchangeable_constSeq p).map_eq_of_ae_tendsto_successFreq (fun _ => measurable_id)
    (ae_of_all _ fun ω => ?_) hμs hμr).symm
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (successFreq_constSeq hN ω).symm

/-! ### The Beta mixture -/

/-- The Beta law gives no mass outside `[0, 1]`. -/
theorem betaMeasure_compl_Icc (α β : ℝ) : betaMeasure α β (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [betaMeasure, withDensity_apply _ measurableSet_Icc.compl]
  refine setLIntegral_eq_zero measurableSet_Icc.compl fun x hx => ?_
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · rw [betaPDF_eq_zero_of_nonpos hx.le]; rfl
  · rw [betaPDF_eq_zero_of_one_le hx.le]; rfl

/-- **The Bernstein moments of the Beta law**: for `α, β > 0` and `s ≤ n`,
`∫ θ^s (1 - θ)^{n-s} dBeta(α, β) = B(α + s, β + n - s) / B(α, β)`. -/
theorem lintegral_bernstein_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n s : ℕ}
    (hs : s ≤ n) :
    ∫⁻ θ, ENNReal.ofReal (θ ^ s * (1 - θ) ^ (n - s)) ∂betaMeasure α β =
      ENNReal.ofReal (beta (α + s) (β + (n - s : ℕ)) / beta α β) := by
  have h := (betaBinomial_normalizedPosterior hα hβ hs).1
  have hc : (0 : ℝ) < n.choose s := by exact_mod_cast Nat.choose_pos hs
  have hae : ∀ᵐ θ ∂betaMeasure α β, θ ∈ Icc (0 : ℝ) 1 := mem_ae_iff.2 (betaMeasure_compl_Icc α β)
  have hpt : (fun x => ENNReal.ofReal (binomPMF n x s)) =ᵐ[betaMeasure α β]
      fun x => ENNReal.ofReal (n.choose s) * ENNReal.ofReal (x ^ s * (1 - x) ^ (n - s)) := by
    filter_upwards [hae] with x hx
    rw [← ENNReal.ofReal_mul hc.le, binomPMF]
    ring_nf
  rw [lintegral_congr_ae hpt, lintegral_const_mul _ (by fun_prop),
    ENNReal.ofReal_mul hc.le] at h
  exact (ENNReal.mul_right_inj (by positivity) ENNReal.ofReal_ne_top).1 h

/-- The probability space of the Beta mixture: `Θ ~ Beta(α, β)` and, independently, i.i.d.
uniform variables `U₀, U₁, …` on `[0, 1]`. -/
noncomputable def betaSeqLaw (α β : ℝ) : Measure (ℝ × (ℕ → I)) :=
  (betaMeasure α β).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))

/-- The **Beta mixture sequence**: `Xᵢ = 1{Uᵢ < Θ}`, with `Θ` clamped to `[0, 1]`. -/
noncomputable def betaSeq (i : ℕ) (ω : ℝ × (ℕ → I)) : Bool :=
  decide (ω.2 i < Set.projIcc 0 1 zero_le_one ω.1)

theorem measurable_betaSeq (i : ℕ) : Measurable (betaSeq i) := by
  have h : MeasurableSet {ω : ℝ × (ℕ → I) | ω.2 i < Set.projIcc 0 1 zero_le_one ω.1} :=
    measurableSet_lt (by fun_prop) (continuous_projIcc.measurable.comp measurable_fst)
  refine measurable_to_bool ?_
  convert h using 1
  ext ω
  simp [betaSeq]

/-- **The pattern probabilities of the Beta mixture**: `P(X₀ = x₀, …, X_{n-1} = x_{n-1})` is
`∫ θ^s (1 - θ)^{n-s} dBeta(α, β)(θ)`. Proof: given `Θ = θ ∈ [0, 1]`, the events `{Uᵢ < θ}` and
`{Uᵢ ≥ θ}` have probabilities `θ` and `1 - θ`, independently over `i` (Fubini and the product
measure of a cylinder). -/
theorem betaSeqLaw_pattern_eq_lintegral (α β : ℝ) {n : ℕ} (x : Fin n → Bool) :
    betaSeqLaw α β {ω | ∀ i : Fin n, betaSeq i ω = x i} =
      ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂betaMeasure α β := by
  have hA : MeasurableSet {ω | ∀ i : Fin n, betaSeq i ω = x i} :=
    measurableSet_pattern (X := fun i : Fin n => betaSeq i) (fun i => measurable_betaSeq i) x
  rw [betaSeqLaw, Measure.prod_apply hA]
  refine lintegral_congr_ae (Filter.Eventually.mono (mem_ae_iff.2 (betaMeasure_compl_Icc α β))
    fun θ hθ => ?_)
  set c : I := Set.projIcc 0 1 zero_le_one θ with hcdef
  have hc : (c : ℝ) = θ := by rw [hcdef, Set.projIcc_of_mem _ hθ]
  set y : ℕ → Bool := fun i => if h : i < n then x ⟨i, h⟩ else true with hydef
  set t : ℕ → Set I := fun i => {v | decide (v < c) = y i} with htdef
  have hset : Prod.mk θ ⁻¹' {ω | ∀ i : Fin n, betaSeq i ω = x i} =
      Set.pi (Finset.range n : Set ℕ) t := by
    ext u
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
      betaSeq, htdef, hydef]
    constructor
    · intro h i hi
      simp only [hi, ↓reduceDIte]
      exact h ⟨i, hi⟩
    · intro h j
      have := h j j.2
      simpa only [j.2, ↓reduceDIte] using this
  have htm : ∀ i ∈ Finset.range n, MeasurableSet (t i) := fun i _ => by
    have hm : Measurable fun v : I => decide (v < c) :=
      measurable_to_bool (by
        convert (measurableSet_lt measurable_id measurable_const : MeasurableSet {v : I | v < c})
          using 1
        ext v
        simp)
    exact hm (measurableSet_singleton _)
  simp only
  rw [hset, Measure.infinitePi_pi (μ := fun _ : ℕ => (volume : Measure I)) htm,
    Finset.prod_range (fun i => volume (t i))]
  have hvol : ∀ j : Fin n, volume (t j) = ENNReal.ofReal (if x j then θ else 1 - θ) := by
    intro j
    have hy : y j = x j := by simp only [hydef, j.2, ↓reduceDIte]
    cases hxj : x j
    · have : t j = Ici c := by
        ext v
        simp [htdef, hy, hxj]
      rw [this, unitInterval.volume_Ici, hc]
      rfl
    · have : t j = Iio c := by
        ext v
        simp [htdef, hy, hxj]
      rw [this, unitInterval.volume_Iio, hc]
      rfl
  simp_rw [hvol]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => by split_ifs <;> linarith [hθ.1, hθ.2]),
    prod_ite_eq_pow_mul_pow]

theorem isProbabilityMeasure_betaSeqLaw {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (betaSeqLaw α β) := by
  have := isProbabilityMeasureBeta hα hβ
  rw [betaSeqLaw]
  infer_instance

instance {α β : ℝ} [Fact (0 < α)] [Fact (0 < β)] : IsProbabilityMeasure (betaSeqLaw α β) :=
  isProbabilityMeasure_betaSeqLaw Fact.out Fact.out

/-- **The beta binomial pattern probabilities**: for `α, β > 0`, the Beta mixture gives the
pattern `x` of length `n` with `s` successes the probability `B(α + s, β + n - s) / B(α, β)`. -/
theorem betaSeq_measure_pattern {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n : ℕ} (x : Fin n → Bool) :
    betaSeqLaw α β {ω | ∀ i : Fin n, betaSeq i ω = x i} =
      ENNReal.ofReal (beta (α + boolCount x) (β + (n - boolCount x : ℕ)) / beta α β) := by
  rw [betaSeqLaw_pattern_eq_lintegral, lintegral_bernstein_betaMeasure hα hβ (boolCount_le x)]

/-- **The Beta mixture is infinitely exchangeable** (the easy direction of de Finetti's
theorem). -/
theorem infExchangeable_betaSeq (α β : ℝ) : InfExchangeable betaSeq (betaSeqLaw α β) :=
  infExchangeable_of_binary_mixture measurable_betaSeq fun _ x =>
    betaSeqLaw_pattern_eq_lintegral α β x

/-- **The mixing law of the Beta mixture is `Beta(α, β)`**: it is the only probability measure on
`[0, 1]` representing the pattern probabilities of the sequence. -/
theorem betaSeq_mixingLaw_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμs : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hμr : ∀ (n : ℕ) (x : Fin n → Bool), betaSeqLaw α β {ω | ∀ i : Fin n, betaSeq i ω = x i} =
      ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂μ) :
    μ = betaMeasure α β := by
  have := isProbabilityMeasure_betaSeqLaw hα hβ
  have := isProbabilityMeasureBeta hα hβ
  obtain ⟨ρ, -, hρu⟩ := (infExchangeable_betaSeq α β).existsUnique_binaryMixture measurable_betaSeq
  exact (hρu μ ⟨inferInstance, hμs, hμr⟩).trans (hρu _ ⟨inferInstance,
    betaMeasure_compl_Icc α β, fun n x => betaSeqLaw_pattern_eq_lintegral α β x⟩).symm

/-- **The limit frequency of the Beta mixture has the law `Beta(α, β)`**: the frequencies converge
almost surely to a measurable limit, and every almost sure limit has the law `Beta(α, β)`. -/
theorem map_limit_betaSeq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (∃ Θ : ℝ × (ℕ → I) → ℝ, Measurable Θ ∧
      ∀ᵐ ω ∂betaSeqLaw α β, Tendsto (fun N => successFreq betaSeq N ω) atTop (𝓝 (Θ ω))) ∧
    ∀ Θ' : ℝ × (ℕ → I) → ℝ,
      (∀ᵐ ω ∂betaSeqLaw α β, Tendsto (fun N => successFreq betaSeq N ω) atTop (𝓝 (Θ' ω))) →
      (betaSeqLaw α β).map Θ' = betaMeasure α β := by
  have := isProbabilityMeasure_betaSeqLaw hα hβ
  have := isProbabilityMeasureBeta hα hβ
  obtain ⟨Θ, hΘm, -, hae, -⟩ :=
    (infExchangeable_betaSeq α β).exists_ae_tendsto_successFreq measurable_betaSeq
  exact ⟨⟨Θ, hΘm, hae⟩, fun Θ' h' =>
    (infExchangeable_betaSeq α β).map_eq_of_ae_tendsto_successFreq measurable_betaSeq h'
      (betaMeasure_compl_Icc α β) fun n x => betaSeqLaw_pattern_eq_lintegral α β x⟩

/-- **Given the limit, the Beta mixture is i.i.d. Bernoulli**: for a measurable almost sure limit
`Θ` of the frequencies, the conditional distribution of `(X₀, …, X_{n-1})` given `Θ` is
`θ ↦ Bernoulli(θ)^{⊗n}` for `Beta(α, β)` almost every `θ`. The positivity of `α` and `β` is
passed as `Fact` instances, so that the conditional distribution is formed under a probability
measure. -/
theorem condDistrib_betaSeq {α β : ℝ} [hα : Fact (0 < α)] [hβ : Fact (0 < β)]
    {Θ : ℝ × (ℕ → I) → ℝ}
    (hΘm : Measurable Θ)
    (hae : ∀ᵐ ω ∂betaSeqLaw α β, Tendsto (fun N => successFreq betaSeq N ω) atTop (𝓝 (Θ ω)))
    (n : ℕ) :
    condDistrib (fun ω (i : Fin n) => betaSeq i ω) Θ (betaSeqLaw α β) =ᵐ[betaMeasure α β]
      bernoulliPiKernel n := by
  have h := (infExchangeable_betaSeq α β).condDistrib_ae_eq_bernoulliPiKernel measurable_betaSeq
    hΘm hae n
  rwa [(map_limit_betaSeq hα.out hβ.out).2 Θ hae] at h

end MetaAnalysis

end CausalInference
