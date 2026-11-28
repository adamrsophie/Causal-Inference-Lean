/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ExchangeableBinaryUnique
public import Mathlib.Analysis.PSeries

/-!
# de Finetti's theorem for binary sequences: almost sure frequencies

For an infinitely exchangeable binary sequence the frequency of successes `S_N / N` converges
almost surely, and the law of the limit is the mixing law:

* if `E|S_N/N - Θ| → 0` with `Θ ∈ [0, 1]`, then `E|S_N/N - Θ| ≤ 1/√N`
  (`InfExchangeable.integral_abs_successFreq_sub_limit_le`); along `N = k⁴` the errors are
  summable, and between consecutive fourth powers the frequency moves by at most
  `1 - (k/(k+1))⁴` (`abs_successFreq_sub_successFreq_le`), so `S_N/N → Θ` almost surely
  (`InfExchangeable.ae_tendsto_successFreq_of_tendsto_integral`);
* **de Finetti's theorem with almost sure frequencies**
  (`InfExchangeable.exists_ae_tendsto_successFreq`): there is a measurable `Θ ∈ [0, 1]` with
  `S_N/N → Θ` almost surely whose law `Π` represents the pattern probabilities,
  `P(X₀ = x₀, …, X_{n-1} = x_{n-1}) = ∫ θ^s (1 - θ)^{n-s} dΠ(θ)`, and is the only law on `[0, 1]`
  that does;
* **the limit has the mixing law** (`InfExchangeable.map_eq_of_ae_tendsto_successFreq`): any
  almost sure limit of the frequencies has the law `Π` of every representing measure
  `Π` on `[0, 1]`. No bound on the limit is assumed.

The argument uses only second moments; it is not the strong law of large numbers for i.i.d.
variables, which does not apply to an exchangeable sequence.

## Main results

* `abs_successFreq_sub_successFreq_le`, `InfExchangeable.integral_abs_successFreq_sub_limit_le`,
  `InfExchangeable.ae_tendsto_successFreq_of_tendsto_integral`,
  `InfExchangeable.exists_ae_tendsto_successFreq`,
  `InfExchangeable.map_eq_of_ae_tendsto_successFreq`.

## References

* B. de Finetti, *La prévision : ses lois logiques, ses sources subjectives*, Annales de
  l'Institut Henri Poincaré 7 (1937).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- **Frequencies of nested windows are close**: for `m ≤ N` with `0 < N`,
`|S_N/N - S_m/m| ≤ (N - m)/N`. Write `S_N = S_m + R` with `0 ≤ R ≤ N - m`; both `R/N` and
`S_m (N - m)/(N m)` lie in `[0, (N - m)/N]`. -/
theorem abs_successFreq_sub_successFreq_le (X : ℕ → Ω → Bool) {m N : ℕ} (hmN : m ≤ N)
    (hN : 0 < N) (ω : Ω) :
    |successFreq X N ω - successFreq X m ω| ≤ ((N : ℝ) - m) / N := by
  set b : ℕ → ℝ := fun i => ((X i ω).toNat : ℝ)
  have hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1 := fun i => toNat_real_mem _
  have hfr : ∀ K, successFreq X K ω = (K : ℝ)⁻¹ * ∑ i ∈ Finset.range K, b i := fun K => rfl
  set A := ∑ i ∈ Finset.range m, b i
  set R := ∑ i ∈ Finset.Ico m N, b i
  have hsplit : ∑ i ∈ Finset.range N, b i = A + R := (Finset.sum_range_add_sum_Ico b hmN).symm
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => (hb i).1
  have hA1 : A ≤ m := by
    calc A ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hb i).2
      _ = m := by simp
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => (hb i).1
  have hR1 : R ≤ (N : ℝ) - m := by
    calc R ≤ ∑ _i ∈ Finset.Ico m N, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hb i).2
      _ = (N : ℝ) - m := by simp [Nat.cast_sub hmN]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  rw [hfr, hfr, hsplit]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [CharP.cast_eq_zero, inv_zero, zero_mul, sub_zero, Finset.range_zero,
      Finset.sum_empty] at hA0 hA1 hR1 ⊢
    have hA : A = 0 := le_antisymm hA1 hA0
    rw [hA, zero_add, abs_of_nonneg (mul_nonneg (inv_nonneg.2 hN'.le) hR0), inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hR1 hN'.le
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hid : (N : ℝ)⁻¹ * (A + R) - (m : ℝ)⁻¹ * A = R / N - A * (N - m) / (N * m) := by
      field_simp
      ring
    rw [hid, abs_sub_le_iff]
    have h1 : R / N ≤ ((N : ℝ) - m) / N := div_le_div_of_nonneg_right hR1 hN'.le
    have h2 : A * (N - m) / (N * m) ≤ ((N : ℝ) - m) / N := by
      rw [div_le_div_iff₀ (by positivity) hN']
      have := mul_le_mul_of_nonneg_right hA1 (sub_nonneg.2 hmN')
      nlinarith
    have h3 : 0 ≤ R / N := by positivity
    have h4 : 0 ≤ A * (N - m) / (N * m) := by
      have := sub_nonneg.2 hmN'
      positivity
    constructor <;> linarith

/-- `|f - g|` is integrable when `f` and `g` are measurable with values in `[0, 1]`. -/
theorem integrable_abs_sub_of_mem_Icc {P : Measure Ω} [IsFiniteMeasure P] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf01 : ∀ ω, f ω ∈ Icc (0 : ℝ) 1)
    (hg01 : ∀ ω, g ω ∈ Icc (0 : ℝ) 1) : Integrable (fun ω => |f ω - g ω|) P :=
  Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 1 (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_abs, abs_sub_le_iff]
    constructor <;> linarith [(hf01 ω).1, (hf01 ω).2, (hg01 ω).1, (hg01 ω).2])

/-- **Rate of the limit in mean**: if `E|S_N/N - Θ| → 0` with `Θ` measurable with values in
`[0, 1]`, then `E|S_N/N - Θ| ≤ 1/√N` for `N ≥ 1`. Let `M → ∞` in
`E|S_N/N - Θ| ≤ E|S_N/N - S_M/M| + E|S_M/M - Θ|`. -/
theorem InfExchangeable.integral_abs_successFreq_sub_limit_le {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {Θ : Ω → ℝ} (hΘm : Measurable Θ) (hΘ : ∀ ω, Θ ω ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto (fun N => ∫ ω, |successFreq X N ω - Θ ω| ∂P) atTop (𝓝 0)) {N : ℕ}
    (hN : 0 < N) :
    ∫ ω, |successFreq X N ω - Θ ω| ∂P ≤ 1 / Real.sqrt N := by
  have hfr := successFreq_mem_Icc X
  have hmf := measurable_successFreq hX
  have h := hlim.const_add (1 / Real.sqrt N)
  rw [add_zero] at h
  refine ge_of_tendsto h ?_
  filter_upwards [eventually_ge_atTop N] with M hM
  calc ∫ ω, |successFreq X N ω - Θ ω| ∂P
      ≤ ∫ ω, (|successFreq X N ω - successFreq X M ω| + |successFreq X M ω - Θ ω|) ∂P :=
        integral_mono (integrable_abs_sub_of_mem_Icc (hmf N) hΘm (hfr N) hΘ)
          ((integrable_abs_sub_of_mem_Icc (hmf N) (hmf M) (hfr N) (hfr M)).add
            (integrable_abs_sub_of_mem_Icc (hmf M) hΘm (hfr M) hΘ)) fun ω => abs_sub_le _ _ _
    _ = ∫ ω, |successFreq X N ω - successFreq X M ω| ∂P + ∫ ω, |successFreq X M ω - Θ ω| ∂P :=
        integral_add (integrable_abs_sub_of_mem_Icc (hmf N) (hmf M) (hfr N) (hfr M))
          (integrable_abs_sub_of_mem_Icc (hmf M) hΘm (hfr M) hΘ)
    _ ≤ 1 / Real.sqrt N + ∫ ω, |successFreq X M ω - Θ ω| ∂P := by
        gcongr
        exact hE.integral_abs_successFreq_sub_le hX hN hM

/-- **Almost sure convergence of the frequencies**: if `E|S_N/N - Θ| → 0` with `Θ` measurable
with values in `[0, 1]`, then `S_N/N → Θ` almost surely. Proof: along `N = k⁴` the means are at
most `1/k²`, so `∑ₖ |S_{k⁴}/k⁴ - Θ|` has finite mean and is finite almost surely; between
consecutive fourth powers `|S_N/N - S_{k⁴}/k⁴| ≤ 1 - (k/(k+1))⁴`. -/
theorem InfExchangeable.ae_tendsto_successFreq_of_tendsto_integral {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {Θ : Ω → ℝ} (hΘm : Measurable Θ) (hΘ : ∀ ω, Θ ω ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto (fun N => ∫ ω, |successFreq X N ω - Θ ω| ∂P) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω)) := by
  set g : ℕ → Ω → ℝ := fun k ω => |successFreq X (k ^ 4) ω - Θ ω| with hg
  have hgm : ∀ k, Measurable (g k) := fun k => by
    have := measurable_successFreq hX (k ^ 4)
    simp only [hg]
    fun_prop
  have hg0 : ∀ k ω, 0 ≤ g k ω := fun k ω => abs_nonneg _
  have hgi : ∀ k, Integrable (g k) P := fun k =>
    integrable_abs_sub_of_mem_Icc (measurable_successFreq hX _) hΘm (successFreq_mem_Icc X _) hΘ
  have hbd : ∀ k, ∫ ω, g k ω ∂P ≤ 4 / ((k : ℝ) + 1) ^ 2 := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      calc ∫ ω, g 0 ω ∂P ≤ ∫ _ω, (1 : ℝ) ∂P :=
            integral_mono (hgi 0) (integrable_const _) fun ω => by
              simp only [hg, abs_sub_le_iff]
              obtain ⟨h1, h2⟩ := successFreq_mem_Icc X (0 ^ 4) ω
              constructor <;> linarith [(hΘ ω).1, (hΘ ω).2]
        _ ≤ 4 / ((0 : ℕ) + 1 : ℝ) ^ 2 := by norm_num
    · have h := hE.integral_abs_successFreq_sub_limit_le hX hΘm hΘ hlim (pow_pos hk 4)
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hs : Real.sqrt ((k ^ 4 : ℕ) : ℝ) = (k : ℝ) ^ 2 := by
        push_cast
        rw [show (k : ℝ) ^ 4 = ((k : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      rw [hs] at h
      refine h.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hsum : Summable fun k : ℕ => 4 / ((k : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa [div_eq_mul_inv] using this.mul_left 4
  have hlt : ∫⁻ ω, ∑' k, ENNReal.ofReal (g k ω) ∂P < ⊤ := by
    rw [lintegral_tsum fun k => (hgm k).ennreal_ofReal.aemeasurable]
    have heq : ∀ k, ∫⁻ ω, ENNReal.ofReal (g k ω) ∂P = ENNReal.ofReal (∫ ω, g k ω ∂P) :=
      fun k => (ofReal_integral_eq_lintegral_ofReal (hgi k) (ae_of_all _ (hg0 k))).symm
    simp_rw [heq]
    calc ∑' k, ENNReal.ofReal (∫ ω, g k ω ∂P)
        ≤ ∑' k : ℕ, ENNReal.ofReal (4 / ((k : ℝ) + 1) ^ 2) :=
          tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hbd k)
      _ = ENNReal.ofReal (∑' k : ℕ, 4 / ((k : ℝ) + 1) ^ 2) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have htm : Measurable fun ω => ∑' k, ENNReal.ofReal (g k ω) := by
    have : (fun ω => ∑' k, ENNReal.ofReal (g k ω)) =
        fun ω => ⨆ n, ∑ k ∈ Finset.range n, ENNReal.ofReal (g k ω) := by
      funext ω
      exact ENNReal.tsum_eq_iSup_nat
    rw [this]
    exact Measurable.iSup fun n => Finset.measurable_sum _ fun k _ => (hgm k).ennreal_ofReal
  have hae := ae_lt_top' htm.aemeasurable hlt.ne
  set κ : ℕ → ℕ := fun N => Nat.sqrt (Nat.sqrt N) with hκ
  have hκlo : ∀ N, κ N ^ 4 ≤ N := fun N => by
    have h1 := Nat.sqrt_le' (Nat.sqrt N)
    have h2 := Nat.sqrt_le' N
    calc κ N ^ 4 = (κ N ^ 2) ^ 2 := by ring
      _ ≤ Nat.sqrt N ^ 2 := Nat.pow_le_pow_left h1 2
      _ ≤ N := h2
  have hκhi : ∀ N, N < (κ N + 1) ^ 4 := fun N => by
    have h1 := Nat.lt_succ_sqrt' (Nat.sqrt N)
    have h2 := Nat.lt_succ_sqrt' N
    calc N < (Nat.sqrt N + 1) ^ 2 := h2
      _ ≤ ((κ N + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (κ N + 1) ^ 4 := by ring
  have hκt : Tendsto κ atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨(b ^ 2) ^ 2, fun N hN => ?_⟩
    exact Nat.le_sqrt'.2 (Nat.le_sqrt'.2 hN)
  set c : ℕ → ℝ := fun k => 1 - ((k : ℝ) / (k + 1)) ^ 4 with hc
  have hct : Tendsto c atTop (𝓝 0) := by
    have h := ((tendsto_natCast_div_add_atTop (1 : ℝ)).pow 4).const_sub 1
    simpa using h
  have hbridge : ∀ N, 0 < N → ∀ ω,
      |successFreq X N ω - successFreq X (κ N ^ 4) ω| ≤ c (κ N) := by
    intro N hN ω
    refine (abs_successFreq_sub_successFreq_le X (hκlo N) hN ω).trans ?_
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hhi : (N : ℝ) ≤ ((κ N : ℝ) + 1) ^ 4 := by exact_mod_cast (hκhi N).le
    have hk1 : (0 : ℝ) < (κ N : ℝ) + 1 := by positivity
    have hid : ((N : ℝ) - ((κ N ^ 4 : ℕ) : ℝ)) / N = 1 - (κ N : ℝ) ^ 4 / N := by
      push_cast
      field_simp
    rw [hid, hc]
    simp only
    rw [div_pow]
    have : (κ N : ℝ) ^ 4 / ((κ N : ℝ) + 1) ^ 4 ≤ (κ N : ℝ) ^ 4 / N :=
      div_le_div_of_nonneg_left (by positivity) hN' hhi
    linarith
  filter_upwards [hae] with ω hω
  have hT : Tendsto (fun k => g k ω) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa [Function.comp_def, ENNReal.toReal_ofReal (hg0 _ ω)] using h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun N => c (κ N) + g (κ N) ω) atTop (𝓝 0) := by
    simpa using (hct.comp hκt).add (hT.comp hκt)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsq
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [Real.norm_eq_abs]
  calc |successFreq X N ω - Θ ω|
      ≤ |successFreq X N ω - successFreq X (κ N ^ 4) ω| + |successFreq X (κ N ^ 4) ω - Θ ω| :=
        abs_sub_le _ _ _
    _ ≤ c (κ N) + g (κ N) ω := add_le_add (hbridge N hN ω) le_rfl

/-- **de Finetti's theorem for binary sequences with almost sure frequencies** (de Finetti 1937):
for an infinitely exchangeable sequence of measurable `Bool` valued variables on a probability
space, the frequency `S_N / N` converges almost surely to a measurable `Θ` with values in
`[0, 1]`; the law `Π = P ∘ Θ⁻¹` represents the pattern probabilities,
`P(X₀ = x₀, …, X_{n-1} = x_{n-1}) = ∫ θ^s (1 - θ)^{n-s} dΠ(θ)` for every pattern with `s`
successes, and every probability measure on `[0, 1]` with this property is `Π`. -/
theorem InfExchangeable.exists_ae_tendsto_successFreq {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) :
    ∃ Θ : Ω → ℝ, Measurable Θ ∧ (∀ ω, Θ ω ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) ∧
      (∀ (n : ℕ) (x : Fin n → Bool), P {ω | ∀ i : Fin n, X i ω = x i} =
        ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂(P.map Θ)) ∧
      ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ (Icc (0 : ℝ) 1)ᶜ = 0 →
        (∀ (n : ℕ) (x : Fin n → Bool), P {ω | ∀ i : Fin n, X i ω = x i} =
          ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂μ) →
        μ = P.map Θ := by
  obtain ⟨Θ, hΘm, hΘ, hlim⟩ := hE.exists_tendsto_integral_abs_successFreq hX
  have hprob : IsProbabilityMeasure (P.map Θ) :=
    (Measure.isProbabilityMeasure_map_iff hΘm.aemeasurable).2 inferInstance
  have hsupp := map_compl_Icc_eq_zero (P := P) hΘm hΘ
  have hrep : ∀ (n : ℕ) (x : Fin n → Bool), P {ω | ∀ i : Fin n, X i ω = x i} =
      ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂(P.map Θ) :=
    fun n x => measure_eq_lintegral_of_measureReal_eq_integral hsupp
      (hE.measureReal_pattern_eq_integral_map hX hΘm hΘ hlim x)
  refine ⟨Θ, hΘm, hΘ, hE.ae_tendsto_successFreq_of_tendsto_integral hX hΘm hΘ hlim, hrep,
    fun μ hμ hμs hμr => ?_⟩
  obtain ⟨ρ, -, hρu⟩ := hE.existsUnique_binaryMixture hX
  exact (hρu μ ⟨hμ, hμs, hμr⟩).trans (hρu _ ⟨hprob, hsupp, hrep⟩).symm

/-- **The limit frequency has the mixing law**: for an infinitely exchangeable binary sequence,
if `Θ'` is an almost sure limit of the frequencies `S_N / N` and `Π` is a probability
measure on `[0, 1]` representing the pattern probabilities, then `Θ'` has the law `Π`. Neither
measurability nor a bound is assumed of `Θ'`: it agrees almost surely with the measurable limit
of `InfExchangeable.exists_ae_tendsto_successFreq`. -/
theorem InfExchangeable.map_eq_of_ae_tendsto_successFreq {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {Θ' : Ω → ℝ}
    (hae : ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ' ω)))
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμs : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hμr : ∀ (n : ℕ) (x : Fin n → Bool), P {ω | ∀ i : Fin n, X i ω = x i} =
      ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂μ) :
    P.map Θ' = μ := by
  obtain ⟨Θ, hΘm, -, hΘae, -, huniq⟩ := hE.exists_ae_tendsto_successFreq hX
  have heq : Θ' =ᵐ[P] Θ := by
    filter_upwards [hae, hΘae] with ω h1 h2
    exact tendsto_nhds_unique h1 h2
  rw [Measure.map_congr heq]
  exact (huniq μ inferInstance hμs hμr).symm

end MetaAnalysis

end CausalInference
