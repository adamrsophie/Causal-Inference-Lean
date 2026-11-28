/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ExchangeableBinaryFrequency
public import CausalInference.MetaAnalysis.ExchangeableBinaryHierarchical
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# de Finetti's theorem for binary sequences: the conditional form

Let `X₀, X₁, …` be infinitely exchangeable `Bool` valued variables and `Θ` an almost sure limit of
the frequencies `S_N / N`, with law `Π`. Given `Θ = θ` the variables are i.i.d. Bernoulli(`θ`):

* **joint law of a pattern and the limit** (`InfExchangeable.measureReal_pattern_inter_preimage`):
  `P(X₀ = x₀, …, X_{n-1} = x_{n-1}, Θ ∈ B) = ∫_B θ^s (1 - θ)^{n-s} dΠ(θ)` for every Borel `B`;
* **conditional probabilities** (`InfExchangeable.condExp_pattern_indicator`):
  `P[X₀ = x₀, …, X_{n-1} = x_{n-1} | σ(Θ)] = Θ^s (1 - Θ)^{n-s}` almost surely, with Mathlib's
  conditional expectation given `MeasurableSpace.comap Θ`;
* **the kernel form** (`InfExchangeable.map_prod_eq_compProd`,
  `InfExchangeable.condDistrib_ae_eq_bernoulliPiKernel`): the joint law of `Θ` and
  `(X₀, …, X_{n-1})` is `Π ⊗ₘ Bernoulli(·)^{⊗n}`, so the conditional distribution of the vector
  given `Θ` (Mathlib's `condDistrib`) is `θ ↦ Bernoulli(θ)^{⊗n}` for `Π` almost every `θ`;
* **the hierarchical form** (`InfExchangeable.map_units_eq_hierarchicalLaw`): the units
  `(Θ, Xᵢ)` have the law `hierarchicalLaw n Π dirac bernoulliClampKernel`.

The limit `Θ` is only assumed measurable; it lies in `[0, 1]` almost surely as a limit of
frequencies. Existence of such a limit is `InfExchangeable.exists_ae_tendsto_successFreq`, and
`InfExchangeable.exists_condDistrib_eq` collects the statements for it.

The proof: on the event `{X₀ = x₀, …, X_{n-1} = x_{n-1}}` the shifted sequence `X_n, X_{n+1}, …`
is again exchangeable and its frequency has the same limit `Θ`, so the moment computation of the
existence proof gives `E[1{pattern} Θᵏ] = E[Θ^{s+k} (1 - Θ)^{n-s}]`; finite measures on `[0, 1]`
are determined by their moments.

## Main results

* `InfExchangeable.measureReal_pattern_inter_preimage`,
  `InfExchangeable.condExp_pattern_indicator`, `InfExchangeable.map_prod_eq_compProd`,
  `InfExchangeable.condDistrib_ae_eq_bernoulliPiKernel`,
  `InfExchangeable.map_units_eq_hierarchicalLaw`, `InfExchangeable.exists_condDistrib_eq`.

## References

* B. de Finetti, *La prévision : ses lois logiques, ses sources subjectives*, Annales de
  l'Institut Henri Poincaré 7 (1937).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Filter Topology Set Function
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- **The shifted frequency has the same limit**: if `S_N/N → t`, then
`(X_n + … + X_{n+N-1})/N → t`. -/
theorem tendsto_successFreq_shift {X : ℕ → Ω → Bool} {ω : Ω} {t : ℝ}
    (h : Tendsto (fun N => successFreq X N ω) atTop (𝓝 t)) (n : ℕ) :
    Tendsto (fun N => successFreq (fun i => X (n + i)) N ω) atTop (𝓝 t) := by
  have hid : ∀ N, 0 < N → successFreq (fun i => X (n + i)) N ω =
      ((n : ℝ) + N) / N * successFreq X (n + N) ω - (n : ℝ) / N * successFreq X n ω := by
    intro N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hs : ∑ i : Fin (n + N), ((X i ω).toNat : ℝ) =
        ∑ i : Fin n, ((X i ω).toNat : ℝ) + ∑ i : Fin N, ((X (n + i) ω).toNat : ℝ) := by
      rw [Fin.sum_univ_add]
      simp
    simp only [successFreq_eq_sum_fin]
    rw [hs]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [CharP.cast_eq_zero, zero_add, Finset.univ_eq_empty, Finset.sum_empty,
        zero_div, zero_mul, sub_zero]
      field_simp
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hnN : (n : ℝ) + N ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  have h1 : Tendsto (fun N : ℕ => ((n : ℝ) + N) / N) atTop (𝓝 1) := by
    have h2 : Tendsto (fun N : ℕ => (n : ℝ) / N + 1) atTop (𝓝 (0 + 1)) :=
      (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_const_nhds
    rw [zero_add] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have h3 : Tendsto (fun N => successFreq X (n + N) ω) atTop (𝓝 t) :=
    h.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
  have h4 : Tendsto (fun N : ℕ => (n : ℝ) / N * successFreq X n ω) atTop
      (𝓝 (0 * successFreq X n ω)) := (tendsto_const_div_atTop_nhds_zero_nat _).mul_const _
  have h5 := (h1.mul h3).sub h4
  rw [one_mul, zero_mul, sub_zero] at h5
  refine h5.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (hid N hN).symm

/-- **Almost sure convergence of the frequencies gives convergence in mean** (dominated
convergence with the bound `1`, for a finite measure and a limit with values in `[0, 1]`). -/
theorem tendsto_integral_abs_successFreq_of_ae {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {ρ : Measure Ω} [IsFiniteMeasure ρ] {Θ : Ω → ℝ} (hΘm : Measurable Θ)
    (hΘ : ∀ ω, Θ ω ∈ Icc (0 : ℝ) 1)
    (h : ∀ᵐ ω ∂ρ, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) :
    Tendsto (fun N => ∫ ω, |successFreq X N ω - Θ ω| ∂ρ) atTop (𝓝 0) := by
  have h0 : ∫ _ω, (0 : ℝ) ∂ρ = 0 := integral_zero _ _
  rw [← h0]
  refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun N => ?_)
    (integrable_const _) (fun N => ae_of_all _ fun ω => ?_) ?_
  · have := measurable_successFreq hX N
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · obtain ⟨h1, h2⟩ := successFreq_mem_Icc X N ω
    rw [Real.norm_eq_abs, abs_abs, abs_sub_le_iff]
    constructor <;> linarith [(hΘ ω).1, (hΘ ω).2]
  · filter_upwards [h] with ω hω
    have := (hω.sub_const (Θ ω)).abs
    simpa using this

/-- **The shifted sequence is exchangeable on a pattern event**: for an infinitely exchangeable
sequence, `X_n, X_{n+1}, …` is infinitely exchangeable under `P` restricted to
`{X₀ = x₀, …, X_{n-1} = x_{n-1}}`. A permutation of `X_n, …, X_{n+N-1}` extends by the identity
to a permutation of the first `n + N` variables, which fixes the pattern event. -/
theorem InfExchangeable.restrict_pattern_shift {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} (hE : InfExchangeable X P) {n : ℕ} (x : Fin n → Bool) :
    InfExchangeable (fun i => X (n + i)) (P.restrict {ω | ∀ j : Fin n, X j ω = x j}) := by
  intro N σ
  let σ' : Equiv.Perm (Fin (n + N)) :=
    finSumFinEquiv.symm.trans (((Equiv.refl (Fin n)).sumCongr σ).trans finSumFinEquiv)
  have hl : ∀ j : Fin n, σ' (Fin.castAdd N j) = Fin.castAdd N j := fun j => by simp [σ']
  have hr : ∀ i : Fin N, σ' (Fin.natAdd n i) = Fin.natAdd n (σ i) := fun i => by simp [σ']
  have hEx := hE (n + N) σ'
  have hm1 : Measurable fun ω (i : Fin N) => X (n + (σ i : ℕ)) ω :=
    measurable_pi_iff.2 fun i => hX _
  have hm2 : Measurable fun ω (i : Fin N) => X (n + (i : ℕ)) ω :=
    measurable_pi_iff.2 fun i => hX _
  have hv1 : Measurable fun ω (k : Fin (n + N)) => X (σ' k) ω := measurable_pi_iff.2 fun k => hX _
  have hv2 : Measurable fun ω (k : Fin (n + N)) => X k ω := measurable_pi_iff.2 fun k => hX _
  change (P.restrict _).map (fun ω (i : Fin N) => X (n + (σ i : ℕ)) ω) =
    (P.restrict _).map (fun ω (i : Fin N) => X (n + (i : ℕ)) ω)
  ext C hC
  rw [Measure.map_apply hm1 hC, Measure.map_apply hm2 hC,
    Measure.restrict_apply (hm1 hC), Measure.restrict_apply (hm2 hC)]
  let D : Set (Fin (n + N) → Bool) :=
    {z | (fun i => z (Fin.natAdd n i)) ∈ C ∧ ∀ j, z (Fin.castAdd N j) = x j}
  have hD : MeasurableSet D := D.toFinite.measurableSet
  have h := congrArg (fun μ : Measure (Fin (n + N) → Bool) => μ D) hEx
  simp only at h
  rw [Measure.map_apply hv1 hD, Measure.map_apply hv2 hD] at h
  convert h using 2
  · ext ω
    simp only [D, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, hl, hr,
      Fin.val_castAdd, Fin.val_natAdd]
  · ext ω
    simp only [D, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      Fin.val_castAdd, Fin.val_natAdd]

/-- Infinite exchangeability is preserved by scaling the measure. -/
theorem InfExchangeable.smul_measure {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} (hE : InfExchangeable X P) (c : ℝ≥0∞) : InfExchangeable X (c • P) := by
  intro N σ
  have h1 : Measurable fun ω (i : Fin N) => X (σ i : ℕ) ω := measurable_pi_iff.2 fun i => hX _
  have h2 : Measurable fun ω (i : Fin N) => X (i : ℕ) ω := measurable_pi_iff.2 fun i => hX _
  have h := hE N σ
  simp only at h ⊢
  rw [Measure.map_smul c h1.aemeasurable, Measure.map_smul c h2.aemeasurable, h]

/-- Appending `k` successes to a pattern adds `k` successes. -/
theorem boolCount_append_true {n : ℕ} (x : Fin n → Bool) (k : ℕ) :
    boolCount (Fin.append x (fun _ : Fin k => true)) = boolCount x + k := by
  simp only [boolCount]
  rw [Fin.sum_univ_add]
  simp

omit [MeasurableSpace Ω] in
theorem setOf_append_true (X : ℕ → Ω → Bool) {n : ℕ} (x : Fin n → Bool) (k : ℕ) :
    {ω | ∀ j : Fin (n + k), X j ω = Fin.append x (fun _ : Fin k => true) j} =
      {ω | ∀ j : Fin k, X (n + j) ω = true} ∩ {ω | ∀ j : Fin n, X j ω = x j} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · simpa using h (Fin.natAdd n j)
    · simpa using h (Fin.castAdd k j)
  · rintro ⟨h1, h2⟩ j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using h2 j
    · simpa using h1 j

/-- **Mixed moments of a pattern and the limit frequency**: if `S_N/N → Θ ∈ [0, 1]` almost
surely, then for a pattern `x` of length `n` with `s` successes,
`E[1{X₀ = x₀, …, X_{n-1} = x_{n-1}} Θᵏ] = E[Θ^{s+k} (1 - Θ)^{n-s}]`. Proof: under `P`
restricted to the pattern event and normalized, the shifted sequence is exchangeable with
frequency limit `Θ`, so its `k`th moment is the probability of `k` further successes. -/
theorem InfExchangeable.setIntegral_pattern_pow {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {Θ : Ω → ℝ} (hΘm : Measurable Θ) (hΘ : ∀ ω, Θ ω ∈ Icc (0 : ℝ) 1)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) {n : ℕ}
    (x : Fin n → Bool) (k : ℕ) :
    ∫ ω in {ω | ∀ j : Fin n, X j ω = x j}, Θ ω ^ k ∂P =
      ∫ ω, Θ ω ^ (boolCount x + k) * (1 - Θ ω) ^ (n - boolCount x) ∂P := by
  set A := {ω | ∀ j : Fin n, X j ω = x j} with hAdef
  set S : Set Ω := {ω | ∀ j : Fin k, X (n + j) ω = true} with hSdef
  have hS : MeasurableSet S := by
    rw [hSdef, Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => (hX _) (measurableSet_singleton true)
  have hlim := tendsto_integral_abs_successFreq_of_ae hX hΘm hΘ hae
  have hR : ∫ ω, Θ ω ^ (boolCount x + k) * (1 - Θ ω) ^ (n - boolCount x) ∂P =
      P.real (S ∩ A) := by
    have h1 := hE.integral_bernstein_limit hX hΘm hΘ hlim (a := boolCount x + k) (n := n + k)
      (by have := boolCount_le x; omega)
    have h2 := hE.measureReal_pattern_eq_sorted hX (Fin.append x (fun _ : Fin k => true))
    rw [boolCount_append_true] at h2
    have h3 : n + k - (boolCount x + k) = n - boolCount x := by omega
    rw [h3] at h1
    rw [h1, ← h2, hSdef, hAdef, ← setOf_append_true]
  rw [hR]
  by_cases h0 : P A = 0
  · rw [Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    have h1 : P.real (S ∩ A) ≤ P.real A := measureReal_mono Set.inter_subset_right
    have h2 : P.real A = 0 := by simp [measureReal_def, h0]
    exact (le_antisymm (h1.trans h2.le) measureReal_nonneg).symm
  · set Q : Measure Ω := (P A)⁻¹ • P.restrict A with hQ
    have hQp : IsProbabilityMeasure Q := ⟨by
      rw [hQ, smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
        ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)]⟩
    have hEQ : InfExchangeable (fun i => X (n + i)) Q :=
      (hE.restrict_pattern_shift hX x).smul_measure (fun i => hX _) _
    have haeQ : ∀ᵐ ω ∂Q, Tendsto (fun N => successFreq (fun i => X (n + i)) N ω) atTop
        (𝓝 (Θ ω)) :=
      Measure.ae_smul_measure (ae_restrict_of_ae (hae.mono fun ω hω =>
        tendsto_successFreq_shift hω n)) _
    have hlimQ := tendsto_integral_abs_successFreq_of_ae (fun i => hX (n + i)) hΘm hΘ haeQ
    have hmom := hEQ.integral_bernstein_limit (fun i => hX (n + i)) hΘm hΘ hlimQ (le_refl k)
    have hpat : Q.real {ω | ∀ j : Fin k, X (n + j) ω = sortedPattern k k j} =
        ((P A)⁻¹).toReal * P.real (S ∩ A) := by
      have hset : {ω | ∀ j : Fin k, X (n + j) ω = sortedPattern k k j} = S := by
        ext ω
        simp [hSdef, sortedPattern]
      rw [hset, hQ, measureReal_def, smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        Measure.restrict_apply hS, measureReal_def]
    rw [hpat, Nat.sub_self, hQ, integral_smul_measure] at hmom
    simp only [pow_zero, mul_one, smul_eq_mul] at hmom
    have hne : ((P A)⁻¹).toReal ≠ 0 := by
      rw [ENNReal.toReal_inv]
      exact inv_ne_zero (ENNReal.toReal_ne_zero.2 ⟨h0, measure_ne_top _ _⟩)
    exact mul_left_cancel₀ hne hmom

/-- The joint law of a pattern and a bounded limit `Θ` (the form with `Θ ∈ [0, 1]` everywhere). -/
theorem InfExchangeable.measureReal_pattern_inter_preimage_of_mem {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {Θ : Ω → ℝ} (hΘm : Measurable Θ) (hΘ : ∀ ω, Θ ω ∈ Icc (0 : ℝ) 1)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) {n : ℕ}
    (x : Fin n → Bool) {B : Set ℝ} (hB : MeasurableSet B) :
    P.real ({ω | ∀ j : Fin n, X j ω = x j} ∩ Θ ⁻¹' B) =
      ∫ θ in B, θ ^ boolCount x * (1 - θ) ^ (n - boolCount x) ∂(P.map Θ) := by
  set w : ℝ → ℝ := fun θ => θ ^ boolCount x * (1 - θ) ^ (n - boolCount x) with hwdef
  have hwm : Measurable w := by fun_prop
  have hsupp : ∀ᵐ θ ∂(P.map Θ), θ ∈ Icc (0 : ℝ) 1 :=
    (ae_map_iff hΘm.aemeasurable measurableSet_Icc).2 (ae_of_all _ hΘ)
  have hPi := map_compl_Icc_eq_zero (P := P) hΘm hΘ
  have hwi : Integrable w (P.map Θ) :=
    Integrable.of_bound hwm.aestronglyMeasurable 1 (by
      filter_upwards [hsupp] with θ hθ
      obtain ⟨h1, h2⟩ := bernstein_mem_Icc hθ (boolCount x) (n - boolCount x)
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact h2)
  set ν₁ : Measure ℝ := (P.restrict {ω | ∀ j : Fin n, X j ω = x j}).map Θ with hν₁
  set ν₂ : Measure ℝ := (P.map Θ).withDensity fun θ => ENNReal.ofReal (w θ) with hν₂
  have : IsFiniteMeasure ν₂ := isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  have heq : ν₁ = ν₂ := by
    refine eq_of_integral_pow_eq_of_isFiniteMeasure ?_ ?_ fun k => ?_
    · rw [hν₁]
      exact map_compl_Icc_eq_zero hΘm hΘ
    · rw [hν₂, withDensity_apply _ measurableSet_Icc.compl]
      exact setLIntegral_measure_zero _ _ hPi
    · rw [hν₁, hν₂, integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
        integral_map hΘm.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop)),
        integral_map hΘm.aemeasurable (Measurable.aestronglyMeasurable (by fun_prop)),
        hE.setIntegral_pattern_pow hX hΘm hΘ hae x k]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [hwdef]
      rw [ENNReal.toReal_ofReal (bernstein_mem_Icc (hΘ ω) _ _).1, smul_eq_mul, pow_add]
      ring
  have hB1 : ν₁ B = P ({ω | ∀ j : Fin n, X j ω = x j} ∩ Θ ⁻¹' B) := by
    rw [hν₁, Measure.map_apply hΘm hB, Measure.restrict_apply (hΘm hB), Set.inter_comm]
  have hB2 : ν₂ B = ∫⁻ θ in B, ENNReal.ofReal (w θ) ∂(P.map Θ) := by
    rw [hν₂, withDensity_apply _ hB]
  rw [measureReal_def, ← hB1, heq, hB2, integral_eq_lintegral_of_nonneg_ae
    (ae_restrict_of_ae (hsupp.mono fun θ hθ => (bernstein_mem_Icc hθ _ _).1))
    hwm.aestronglyMeasurable]

/-- A measurable almost sure limit of frequencies agrees almost surely with its clamp to
`[0, 1]`. -/
theorem ae_eq_clamp_of_ae_tendsto_successFreq {X : ℕ → Ω → Bool} {P : Measure Ω} {Θ : Ω → ℝ}
    (hae : ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) :
    (fun ω => max 0 (min 1 (Θ ω))) =ᵐ[P] Θ := by
  filter_upwards [hae] with ω hω
  have hmem : Θ ω ∈ Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hω (Eventually.of_forall fun N => successFreq_mem_Icc X N ω)
  rw [min_eq_right hmem.2, max_eq_right hmem.1]

/-- **de Finetti, joint law of a pattern and the limit frequency**: let `Θ` be a measurable
almost sure limit of the frequencies of an infinitely exchangeable binary sequence and
`Π = P ∘ Θ⁻¹`. For every pattern `x` of length `n` with `s` successes and every Borel `B`,
`P(X₀ = x₀, …, X_{n-1} = x_{n-1}, Θ ∈ B) = ∫_B θ^s (1 - θ)^{n-s} dΠ(θ)`. -/
theorem InfExchangeable.measureReal_pattern_inter_preimage {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {Θ : Ω → ℝ} (hΘm : Measurable Θ)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) {n : ℕ}
    (x : Fin n → Bool) {B : Set ℝ} (hB : MeasurableSet B) :
    P.real ({ω | ∀ j : Fin n, X j ω = x j} ∩ Θ ⁻¹' B) =
      ∫ θ in B, θ ^ boolCount x * (1 - θ) ^ (n - boolCount x) ∂(P.map Θ) := by
  set Θ' : Ω → ℝ := fun ω => max 0 (min 1 (Θ ω))
  have heq := ae_eq_clamp_of_ae_tendsto_successFreq hae
  have hΘ'm : Measurable Θ' := by fun_prop
  have hΘ' : ∀ ω, Θ' ω ∈ Icc (0 : ℝ) 1 :=
    fun ω => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hae' : ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ' ω)) := by
    filter_upwards [hae, heq] with ω h1 h2
    change Tendsto _ atTop (𝓝 (max 0 (min 1 (Θ ω))))
    rwa [h2]
  have h := hE.measureReal_pattern_inter_preimage_of_mem hX hΘ'm hΘ' hae' x hB
  rw [Measure.map_congr heq] at h
  rw [← h]
  refine measureReal_congr ?_
  filter_upwards [heq] with ω hω
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  rw [show Θ' ω = Θ ω from hω]

/-- **de Finetti, conditional form**: given `Θ` the variables are i.i.d. Bernoulli(`Θ`). If `Θ` is
a measurable almost sure limit of the frequencies of an infinitely exchangeable binary sequence,
then for every pattern `x` of length `n` with `s` successes,
`P[X₀ = x₀, …, X_{n-1} = x_{n-1} | σ(Θ)] = Θ^s (1 - Θ)^{n-s}` almost surely. Proof: both sides
have the same integral over every set `{Θ ∈ B}` of `σ(Θ)`, by the joint law, and the right side is
`σ(Θ)` measurable. -/
theorem InfExchangeable.condExp_pattern_indicator {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {Θ : Ω → ℝ} (hΘm : Measurable Θ)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) {n : ℕ}
    (x : Fin n → Bool) :
    (fun ω => Θ ω ^ boolCount x * (1 - Θ ω) ^ (n - boolCount x)) =ᵐ[P]
      P[{ω | ∀ j : Fin n, X j ω = x j}.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap Θ inferInstance] := by
  have hm : MeasurableSpace.comap Θ inferInstance ≤ ‹MeasurableSpace Ω› := hΘm.comap_le
  have hA := measurableSet_pattern (X := fun i : Fin n => X i) (fun i => hX i) x
  have hwm : Measurable fun θ : ℝ => θ ^ boolCount x * (1 - θ) ^ (n - boolCount x) := by
    fun_prop
  have hmem : ∀ᵐ ω ∂P, Θ ω ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hae] with ω hω
    exact isClosed_Icc.mem_of_tendsto hω
      (Eventually.of_forall fun N => successFreq_mem_Icc X N ω)
  have hgi : Integrable (fun ω => Θ ω ^ boolCount x * (1 - Θ ω) ^ (n - boolCount x)) P :=
    Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 1 (by
      filter_upwards [hmem] with ω hω
      obtain ⟨h1, h2⟩ := bernstein_mem_Icc hω (boolCount x) (n - boolCount x)
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact h2)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm ((integrable_const (1 : ℝ)).indicator hA)
    (fun t _ _ => hgi.integrableOn) ?_ ?_
  · rintro t ⟨B, hB, rfl⟩ _
    rw [setIntegral_indicator hA, setIntegral_const, smul_eq_mul, mul_one,
      ← setIntegral_map hB hwm.aestronglyMeasurable hΘm.aemeasurable,
      ← hE.measureReal_pattern_inter_preimage hX hΘm hae x hB, Set.inter_comm]
  · exact (hwm.comp (comap_measurable Θ)).aestronglyMeasurable

/-! ### The kernel and hierarchical forms -/

/-- **The joint law of the limit and the first `n` variables**: if `Θ` is a measurable almost
sure limit of the frequencies, the law of `(Θ, (X₀, …, X_{n-1}))` is
`Π ⊗ₘ Bernoulli(·)^{⊗n}` with `Π = P ∘ Θ⁻¹`. -/
theorem InfExchangeable.map_prod_eq_compProd {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} [IsProbabilityMeasure P] (hE : InfExchangeable X P) {Θ : Ω → ℝ}
    (hΘm : Measurable Θ)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) (n : ℕ) :
    P.map (fun ω => (Θ ω, fun i : Fin n => X i ω)) = P.map Θ ⊗ₘ bernoulliPiKernel n := by
  classical
  have hv : Measurable fun ω (i : Fin n) => X i ω := measurable_pi_iff.2 fun i => hX i
  have hpair : Measurable fun ω => (Θ ω, fun i : Fin n => X i ω) := hΘm.prodMk hv
  have hsupp : (P.map Θ) (Icc (0 : ℝ) 1)ᶜ = 0 := by
    have heq := ae_eq_clamp_of_ae_tendsto_successFreq hae
    rw [← Measure.map_congr heq]
    exact map_compl_Icc_eq_zero (by fun_prop) fun ω =>
      ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  refine Measure.ext_prod fun {s t} hs ht => ?_
  rw [Measure.map_apply hpair (hs.prod ht), Measure.compProd_apply_prod hs ht]
  have hpre : (fun ω => (Θ ω, fun i : Fin n => X i ω)) ⁻¹' (s ×ˢ t) =
      ⋃ x ∈ t.toFinset, ({ω | ∀ j : Fin n, X j ω = x j} ∩ Θ ⁻¹' s) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_toFinset, exists_prop, Set.mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨_, h2, fun _ => rfl, h1⟩, fun ⟨x, hx, h, h1⟩ => ⟨h1, by
      rwa [show (fun j : Fin n => X j ω) = x from funext h]⟩⟩
  have hK : ∀ θ, bernoulliPiKernel n θ t = ∑ x ∈ t.toFinset, bernoulliPiKernel n θ {x} := by
    intro θ
    conv_lhs => rw [← Set.coe_toFinset t, ← MeasureTheory.sum_measure_singleton]
  rw [hpre, measure_biUnion_finset]
  · simp_rw [hK]
    rw [lintegral_finsetSum _ fun x _ => Kernel.measurable_coe _ (measurableSet_singleton x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h := hE.measureReal_pattern_inter_preimage hX hΘm hae x hs
    rw [← ofReal_measureReal (measure_ne_top _ _), h,
      ofReal_integral_eq_lintegral_ofReal]
    · refine setLIntegral_congr_fun_ae hs ?_
      filter_upwards [mem_ae_iff.2 hsupp] with θ hθ _
      exact (bernoulliPiKernel_singleton hθ x).symm
    · refine Integrable.of_bound (by fun_prop) 1 ?_
      filter_upwards [ae_restrict_of_ae (mem_ae_iff.2 hsupp)] with θ hθ
      obtain ⟨h1, h2⟩ := bernstein_mem_Icc hθ (boolCount x) (n - boolCount x)
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact h2
    · filter_upwards [ae_restrict_of_ae (mem_ae_iff.2 hsupp)] with θ hθ
      exact (bernstein_mem_Icc hθ _ _).1
  · intro x _ y _ hxy
    refine Set.disjoint_left.2 fun ω h1 h2 => hxy (funext fun j => ?_)
    rw [← h1.1 j, ← h2.1 j]
  · exact fun x _ => (measurableSet_pattern (X := fun i : Fin n => X i) (fun i => hX i) x).inter
      (hΘm hs)

/-- **The conditional distribution given the limit is i.i.d. Bernoulli**: if `Θ` is a measurable
almost sure limit of the frequencies of an infinitely exchangeable binary sequence, the
conditional distribution of `(X₀, …, X_{n-1})` given `Θ` is `θ ↦ Bernoulli(θ)^{⊗n}` for almost
every `θ` under the law of `Θ`. -/
theorem InfExchangeable.condDistrib_ae_eq_bernoulliPiKernel {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {Θ : Ω → ℝ} (hΘm : Measurable Θ)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) (n : ℕ) :
    condDistrib (fun ω (i : Fin n) => X i ω) Θ P =ᵐ[P.map Θ] bernoulliPiKernel n :=
  condDistrib_ae_eq_of_measure_eq_compProd hΘm.aemeasurable
    (measurable_pi_iff.2 fun (i : Fin n) => hX i).aemeasurable
    (hE.map_prod_eq_compProd hX hΘm hae n)

/-- **The units `(Θ, Xᵢ)` follow the hierarchical model**: if `Θ` is a measurable almost sure
limit of the frequencies of an infinitely exchangeable binary sequence, the law of
`((Θ, X₀), …, (Θ, X_{n-1}))` is `hierarchicalLaw n Π dirac bernoulliClampKernel` with `Π = P ∘ Θ⁻¹`:
the hyperparameter `Θ ~ Π` is the parameter of every unit, and given it the outcomes are i.i.d.
Bernoulli(`Θ`). -/
theorem InfExchangeable.map_units_eq_hierarchicalLaw {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {Θ : Ω → ℝ} (hΘm : Measurable Θ)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) (n : ℕ) :
    P.map (fun ω (i : Fin n) => (Θ ω, X i ω)) =
      hierarchicalLaw n (P.map Θ) (fun φ => Measure.dirac φ) bernoulliClampKernel := by
  have hv : Measurable fun ω (i : Fin n) => X i ω := measurable_pi_iff.2 fun i => hX i
  have hG : Measurable fun p : ℝ × (Fin n → Bool) => fun i => (p.1, p.2 i) := by fun_prop
  have hcomp : (fun ω (i : Fin n) => (Θ ω, X i ω)) =
      (fun p : ℝ × (Fin n → Bool) => fun i => (p.1, p.2 i)) ∘
        fun ω => (Θ ω, fun i : Fin n => X i ω) := rfl
  have hF : (fun φ => Measure.pi fun _ : Fin n => Measure.dirac φ ⊗ₘ bernoulliClampKernel) =
      fun φ => (bernoulliPiKernel n φ).map (fun y i => (φ, y i)) := by
    funext φ
    rw [pi_dirac_compProd_eq_map, bernoulliPiKernel_apply]
  have hFm : Measurable fun φ => (bernoulliPiKernel n φ).map (fun y (i : Fin n) => (φ, y i)) := by
    rw [← hF]
    exact measurable_pi_dirac_compProd bernoulliClampKernel n (bernoulliPiKernel n)
      (bernoulliPiKernel_apply n)
  rw [hcomp, ← Measure.map_map hG (hΘm.prodMk hv), hE.map_prod_eq_compProd hX hΘm hae n,
    hierarchicalLaw, hF]
  ext A hA
  rw [Measure.map_apply hG hA, Measure.compProd_apply (hG hA), Measure.bind_apply hA
    hFm.aemeasurable]
  refine lintegral_congr fun φ => ?_
  rw [Measure.map_apply (by fun_prop) hA]
  rfl

/-- **de Finetti's theorem for binary sequences, conditional form** (de Finetti 1937): for an
infinitely exchangeable sequence of measurable `Bool` valued variables on a probability space
there is a measurable `Θ` with values in `[0, 1]` such that `S_N / N → Θ` almost surely and, for
every `n`, given `Θ` the variables `X₀, …, X_{n-1}` are i.i.d. Bernoulli(`Θ`): the conditional
distribution of `(X₀, …, X_{n-1})` given `Θ` is `θ ↦ Bernoulli(θ)^{⊗n}` almost everywhere,
`P[X₀ = x₀, …, X_{n-1} = x_{n-1} | σ(Θ)] = Θ^s (1 - Θ)^{n-s}` almost surely for every pattern with
`s` successes, and the units `(Θ, Xᵢ)` have the law `hierarchicalLaw n (P ∘ Θ⁻¹) dirac
bernoulliClampKernel`. -/
theorem InfExchangeable.exists_condDistrib_eq {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} [IsProbabilityMeasure P] (hE : InfExchangeable X P) :
    ∃ Θ : Ω → ℝ, Measurable Θ ∧ (∀ ω, Θ ω ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ ω ∂P, Tendsto (fun N => successFreq X N ω) atTop (𝓝 (Θ ω))) ∧
      (∀ n : ℕ, condDistrib (fun ω (i : Fin n) => X i ω) Θ P =ᵐ[P.map Θ] bernoulliPiKernel n) ∧
      (∀ (n : ℕ) (x : Fin n → Bool),
        (fun ω => Θ ω ^ boolCount x * (1 - Θ ω) ^ (n - boolCount x)) =ᵐ[P]
          P[{ω | ∀ j : Fin n, X j ω = x j}.indicator (fun _ => (1 : ℝ)) |
            MeasurableSpace.comap Θ inferInstance]) ∧
      ∀ n : ℕ, P.map (fun ω (i : Fin n) => (Θ ω, X i ω)) =
        hierarchicalLaw n (P.map Θ) (fun φ => Measure.dirac φ) bernoulliClampKernel := by
  obtain ⟨Θ, hΘm, hΘ, hae, -⟩ := hE.exists_ae_tendsto_successFreq hX
  exact ⟨Θ, hΘm, hΘ, hae, fun n => hE.condDistrib_ae_eq_bernoulliPiKernel hX hΘm hae n,
    fun n x => hE.condExp_pattern_indicator hX hΘm hae x,
    fun n => hE.map_units_eq_hierarchicalLaw hX hΘm hae n⟩

end MetaAnalysis

end CausalInference
