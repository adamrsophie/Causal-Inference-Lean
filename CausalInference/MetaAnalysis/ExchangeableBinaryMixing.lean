/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ExchangeableBinaryFinite
public import CausalInference.Estimation.Estimator
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# de Finetti's theorem for binary sequences: existence of the mixing law

Let `X₀, X₁, …` be an infinitely exchangeable sequence of `Bool` valued random variables and
`S_N / N` the frequency of successes among the first `N` (`successFreq`, the sample mean of the
`0/1` values). Then:

* the frequencies are Cauchy in mean square: `E[(S_N/N - S_M/M)²] ≤ 1/N` for `1 ≤ N ≤ M`
  (`InfExchangeable.integral_sq_successFreq_sub_le`), so they converge in `L¹` to a measurable
  `Θ` with values in `[0, 1]` (`InfExchangeable.exists_tendsto_integral_abs_successFreq`);
* `E[(S_N/N)^a (1 - S_N/N)^{n-a}]` is an average of pattern probabilities over all index maps
  `Fin n → Fin N`; for injective maps these equal the probability of the sorted pattern, and the
  fraction of non injective maps tends to `0`
  (`InfExchangeable.tendsto_integral_successFreq_bernstein`);
* hence `E[Θ^a (1 - Θ)^{n-a}]` is the probability of the sorted pattern with `a` successes
  (`InfExchangeable.integral_bernstein_limit`), and every pattern has the probability of the
  sorted one with the same number of successes.

**de Finetti's theorem, existence** (`InfExchangeable.exists_binaryMixture`): there is a
probability measure `Π` on `ℝ` concentrated on `[0, 1]` (the law of `Θ`) with
`P(X₀ = x₀, …, X_{n-1} = x_{n-1}) = ∫ θ^s (1 - θ)^{n-s} dΠ(θ)` for every `n` and every pattern
`x` with `s` successes. With the easy direction `infExchangeable_of_binary_mixture` this gives a
characterization (`infExchangeable_iff_exists_binaryMixture`).

The proof uses second moments and the completeness of `L¹`, not Hausdorff's moment theorem or
the compactness of the probability measures on `[0, 1]`.

## Main definitions

* `successFreq`.

## Main results

* `InfExchangeable.tendsto_integral_successFreq_bernstein`,
  `InfExchangeable.exists_tendsto_integral_abs_successFreq`,
  `InfExchangeable.integral_bernstein_limit`, `InfExchangeable.exists_binaryMixture`,
  `infExchangeable_iff_exists_binaryMixture`.

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

/-- The **frequency of successes** `S_N / N` among `X₀, …, X_{N-1}`: the sample mean of the
`0/1` values. -/
noncomputable def successFreq (X : ℕ → Ω → Bool) (N : ℕ) (ω : Ω) : ℝ :=
  sampleMean (fun b : Bool => (b.toNat : ℝ)) X N ω

omit [MeasurableSpace Ω] in
theorem successFreq_eq_sum_fin (X : ℕ → Ω → Bool) (N : ℕ) (ω : Ω) :
    successFreq X N ω = (N : ℝ)⁻¹ * ∑ i : Fin N, ((X i ω).toNat : ℝ) := by
  rw [successFreq, sampleMean, Fin.sum_univ_eq_sum_range (fun i => ((X i ω).toNat : ℝ))]

theorem toNat_real_mem (b : Bool) : 0 ≤ (b.toNat : ℝ) ∧ (b.toNat : ℝ) ≤ 1 := by
  cases b <;> simp

theorem measurable_successFreq {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i)) (N : ℕ) :
    Measurable (successFreq X N) := by
  have : successFreq X N = fun ω => (N : ℝ)⁻¹ * ∑ i : Fin N, ((X i ω).toNat : ℝ) :=
    funext (successFreq_eq_sum_fin X N)
  rw [this]
  exact (Finset.measurable_sum _ fun i _ =>
    (measurable_of_finite (fun b : Bool => (b.toNat : ℝ))).comp (hX _)).const_mul _

omit [MeasurableSpace Ω] in
/-- `0 ≤ S_N/N ≤ 1`. -/
theorem successFreq_mem_Icc (X : ℕ → Ω → Bool) (N : ℕ) (ω : Ω) :
    successFreq X N ω ∈ Icc (0 : ℝ) 1 := by
  rw [successFreq_eq_sum_fin]
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (toNat_real_mem _).1)
  · rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      simp
    · have hs : ∑ i : Fin N, ((X i ω).toNat : ℝ) ≤ N := by
        calc ∑ i : Fin N, ((X i ω).toNat : ℝ) ≤ ∑ _i : Fin N, (1 : ℝ) :=
              Finset.sum_le_sum fun _ _ => (toNat_real_mem _).2
          _ = N := by simp
      rw [inv_mul_le_iff₀ (by exact_mod_cast h)]
      linarith

omit [MeasurableSpace Ω] in
theorem abs_successFreq_le (X : ℕ → Ω → Bool) (N : ℕ) (ω : Ω) : |successFreq X N ω| ≤ 1 := by
  obtain ⟨h1, h2⟩ := successFreq_mem_Icc X N ω
  rw [abs_of_nonneg h1]
  exact h2

/-! ### Pattern probabilities along index maps -/

/-- A product of coordinate indicators is the indicator of the pattern. -/
theorem prod_ite_eq_ite_eq {n : ℕ} (c x : Fin n → Bool) :
    ∏ j, (if x j = c j then (1 : ℝ) else 0) = if x = c then 1 else 0 := by
  rw [Finset.prod_boole]
  simp [funext_iff]

theorem abs_prod_ite_le {n : ℕ} (c x : Fin n → Bool) :
    |∏ j, (if x j = c j then (1 : ℝ) else 0)| ≤ 1 := by
  rw [prod_ite_eq_ite_eq]
  split_ifs <;> simp

theorem measurable_prod_ite {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i)) {n N : ℕ}
    (τ : Fin n → Fin N) (c : Fin n → Bool) :
    Measurable fun ω => ∏ j, (if X (τ j) ω = c j then (1 : ℝ) else 0) :=
  Finset.measurable_prod _ fun j _ =>
    (measurable_of_finite (fun b : Bool => if b = c j then (1 : ℝ) else 0)).comp (hX _)

/-- The expectation of a product of coordinate indicators is the probability of the pattern. -/
theorem integral_prod_ite_eq {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i)) {P : Measure Ω}
    [IsFiniteMeasure P] {n N : ℕ} (τ : Fin n → Fin N) (c : Fin n → Bool) :
    ∫ ω, ∏ j, (if X (τ j) ω = c j then (1 : ℝ) else 0) ∂P =
      P.real {ω | ∀ j, X (τ j) ω = c j} := by
  have hA : MeasurableSet {ω | ∀ j, X (τ j) ω = c j} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => (hX _) (measurableSet_singleton (c j))
  rw [← integral_indicator_one hA]
  congr 1
  funext ω
  rw [prod_ite_eq_ite_eq (c := c) (x := fun j => X (τ j) ω)]
  simp [Set.indicator, funext_iff]

/-- Pattern probabilities of an infinitely exchangeable sequence along an injective index map are
those of the first coordinates. -/
theorem InfExchangeable.measureReal_pattern_comp_injective {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} (hE : InfExchangeable X P) {n N : ℕ}
    {τ : Fin n → Fin N} (hτ : Injective τ) (c : Fin n → Bool) :
    P.real {ω | ∀ j, X (τ j) ω = c j} = P.real {ω | ∀ j : Fin n, X j ω = c j} := by
  have h := congrArg (fun μ : Measure (Fin n → Bool) => μ.real {c})
    (hE.map_comp_injective hX hτ)
  have hv : Measurable fun ω (j : Fin n) => X (τ j) ω := measurable_pi_iff.2 fun j => hX _
  have hv' : Measurable fun ω (j : Fin n) => X j ω := measurable_pi_iff.2 fun j => hX _
  rw [map_measureReal_apply hv (measurableSet_singleton c),
    map_measureReal_apply hv' (measurableSet_singleton c)] at h
  convert h using 2 <;> ext ω <;> simp [funext_iff]

/-- Pattern probabilities of an infinitely exchangeable binary sequence are those of the sorted
pattern with the same number of successes. -/
theorem InfExchangeable.measureReal_pattern_eq_sorted {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} (hE : InfExchangeable X P) {n : ℕ}
    (x : Fin n → Bool) :
    P.real {ω | ∀ j : Fin n, X j ω = x j} =
      P.real {ω | ∀ j : Fin n, X j ω = sortedPattern (boolCount x) n j} := by
  rw [measureReal_def, measureReal_def,
    (hE n).measure_pattern_eq_sorted (X := fun i : Fin n => X i) (fun i => hX i) x]

omit [MeasurableSpace Ω] in
/-- The product of averaged indicators is `(S_N/N)^a (1 - S_N/N)^{n-a}`. -/
theorem prod_avg_ite_eq_successFreq (X : ℕ → Ω → Bool) {a n N : ℕ} (han : a ≤ n) (hN : 0 < N)
    (ω : Ω) :
    ∏ j : Fin n, ((N : ℝ)⁻¹ * ∑ i : Fin N, (if X i ω = sortedPattern a n j then (1 : ℝ) else 0)) =
      successFreq X N ω ^ a * (1 - successFreq X N ω) ^ (n - a) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : (N : ℝ)⁻¹ * ∑ i : Fin N, (if X i ω = true then (1 : ℝ) else 0) =
      successFreq X N ω := by
    rw [successFreq_eq_sum_fin]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    cases X i ω <;> simp
  have h0 : (N : ℝ)⁻¹ * ∑ i : Fin N, (if X i ω = false then (1 : ℝ) else 0) =
      1 - successFreq X N ω := by
    have : ∀ i : Fin N, (if X i ω = false then (1 : ℝ) else 0) = 1 - ((X i ω).toNat : ℝ) :=
      fun i => by cases X i ω <;> simp
    simp only [successFreq_eq_sum_fin, this, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  have hf : ∀ j : Fin n, (N : ℝ)⁻¹ * ∑ i : Fin N,
      (if X i ω = sortedPattern a n j then (1 : ℝ) else 0) =
      if j.val < a then successFreq X N ω else 1 - successFreq X N ω := fun j => by
    by_cases hj : j.val < a
    · simp only [sortedPattern, hj, decide_true, ite_true, h1]
    · simp only [sortedPattern, hj, decide_false, ite_false, h0]
  simp only [hf]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hc : (Finset.univ.filter fun j : Fin n => j.val < a).card = a := by
    rw [Fin.card_filter_val_lt, min_eq_right han]
  have hc' : (Finset.univ.filter fun j : Fin n => ¬ j.val < a).card = n - a := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j : Fin n => j.val < a)
    rw [hc, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [hc, hc']

/-- The number of injective maps `Fin n → Fin N` is `N (N - 1) ⋯ (N - n + 1)`. -/
theorem card_filter_injective_fin (n N : ℕ) :
    (Finset.univ.filter fun τ : Fin n → Fin N => Injective τ).card = N.descFactorial n := by
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

/-- `E[(S_N/N)^a (1 - S_N/N)^{n-a}]` is the average of the pattern probabilities
`P(X_{τ 0}, …, X_{τ (n-1)} = sorted pattern)` over all `τ : Fin n → Fin N`. -/
theorem integral_successFreq_bernstein_eq_sum {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} [IsFiniteMeasure P] {a n N : ℕ} (han : a ≤ n) (hN : 0 < N) :
    ∫ ω, successFreq X N ω ^ a * (1 - successFreq X N ω) ^ (n - a) ∂P =
      ∑ τ : Fin n → Fin N, ((N : ℝ)⁻¹) ^ n *
        P.real {ω | ∀ j, X (τ j) ω = sortedPattern a n j} := by
  have hpt : ∀ ω, successFreq X N ω ^ a * (1 - successFreq X N ω) ^ (n - a) =
      ∑ τ : Fin n → Fin N, ((N : ℝ)⁻¹) ^ n *
        ∏ j, (if X (τ j) ω = sortedPattern a n j then (1 : ℝ) else 0) := fun ω => by
    rw [← prod_avg_ite_eq_successFreq X han hN ω]
    simp_rw [Finset.mul_sum]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hint : ∀ τ : Fin n → Fin N, Integrable (fun ω => ((N : ℝ)⁻¹) ^ n *
      ∏ j, (if X (τ j) ω = sortedPattern a n j then (1 : ℝ) else 0)) P := fun τ =>
    (Integrable.of_bound (measurable_prod_ite hX τ _).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_prod_ite_le (sortedPattern a n) fun j => X (τ j) ω)).const_mul _
  simp_rw [hpt]
  rw [integral_finsetSum _ fun τ _ => hint τ]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_prod_ite_eq hX]

/-- **Moments of the frequency converge to pattern probabilities**: for an infinitely
exchangeable binary sequence and `a ≤ n`, `E[(S_N/N)^a (1 - S_N/N)^{n-a}]` tends to the
probability of the sorted pattern with `a` successes. Proof: the expectation averages pattern
probabilities over all `τ : Fin n → Fin N`; for injective `τ` each is the target, and the fraction
of the other maps is `1 - N(N-1)⋯(N-n+1)/Nⁿ ≤ 1 - ((N+1-n)/N)ⁿ → 0`. -/
theorem InfExchangeable.tendsto_integral_successFreq_bernstein {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {a n : ℕ} (han : a ≤ n) :
    Tendsto (fun N => ∫ ω, successFreq X N ω ^ a * (1 - successFreq X N ω) ^ (n - a) ∂P)
      atTop (𝓝 (P.real {ω | ∀ j : Fin n, X j ω = sortedPattern a n j})) := by
  set p := P.real {ω | ∀ j : Fin n, X j ω = sortedPattern a n j} with hp
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have key : ∀ N, 0 < N →
      |∫ ω, successFreq X N ω ^ a * (1 - successFreq X N ω) ^ (n - a) ∂P - p| ≤
      2 * (1 - ((N : ℝ)⁻¹) ^ n * N.descFactorial n) := by
    intro N hN
    set c : ℝ := ((N : ℝ)⁻¹) ^ n with hc
    have hcT : c * (N : ℝ) ^ n = 1 := by
      rw [hc, ← mul_pow, inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_pow]
    set e : (Fin n → Fin N) → ℝ := fun τ => P.real {ω | ∀ j, X (τ j) ω = sortedPattern a n j}
    have hterm : ∀ τ, |e τ - (if Injective τ then p else 0)| ≤
        if Injective τ then 0 else 1 := by
      intro τ
      split_ifs with hτ
      · simp [e, hE.measureReal_pattern_comp_injective hX hτ, hp]
      · simp only [sub_zero, e]
        rw [abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one
    have hsumI : ∑ τ : Fin n → Fin N, (if Injective τ then p else 0) =
        (N.descFactorial n : ℝ) * p := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
        card_filter_injective_fin]
    have hsumN : ∑ τ : Fin n → Fin N, (if Injective τ then (0 : ℝ) else 1) =
        (N : ℝ) ^ n - N.descFactorial n := by
      have h1 : ∑ τ : Fin n → Fin N, (if Injective τ then (0 : ℝ) else 1) =
          ∑ τ : Fin n → Fin N, (1 - if Injective τ then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun τ _ => by split_ifs <;> simp
      rw [h1, Finset.sum_sub_distrib, Finset.sum_boole, card_filter_injective_fin,
        Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      push_cast
      ring
    have hbound : |∑ τ, (e τ - (if Injective τ then p else 0))| ≤
        (N : ℝ) ^ n - N.descFactorial n := by
      rw [← hsumN]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => hterm τ)
    have hr1 : c * N.descFactorial n ≤ 1 := by
      rw [← hcT]
      gcongr
      exact_mod_cast Nat.descFactorial_le_pow N n
    rw [integral_successFreq_bernstein_eq_sum hX han hN, ← Finset.mul_sum]
    have hdecomp : c * ∑ τ, e τ - p =
        c * ∑ τ, (e τ - (if Injective τ then p else 0)) - (1 - c * N.descFactorial n) * p := by
      rw [Finset.sum_sub_distrib, hsumI]
      ring
    rw [hdecomp]
    have hc0 : 0 ≤ c := by positivity
    calc |c * ∑ τ, (e τ - (if Injective τ then p else 0)) - (1 - c * N.descFactorial n) * p|
        ≤ |c * ∑ τ, (e τ - (if Injective τ then p else 0))| +
            |(1 - c * N.descFactorial n) * p| := abs_sub _ _
      _ ≤ c * ((N : ℝ) ^ n - N.descFactorial n) + (1 - c * N.descFactorial n) * 1 := by
          rw [abs_mul, abs_of_nonneg hc0, abs_mul, abs_of_nonneg hp0,
            abs_of_nonneg (sub_nonneg.2 hr1)]
          exact add_le_add (mul_le_mul_of_nonneg_left hbound hc0)
            (mul_le_mul_of_nonneg_left hp1 (sub_nonneg.2 hr1))
      _ = 2 * (1 - c * N.descFactorial n) := by
          rw [mul_sub, hcT]
          ring
  have hlow : ∀ N, n ≤ N → 0 < N →
      ((N + 1 - n : ℝ) / N) ^ n ≤ ((N : ℝ)⁻¹) ^ n * N.descFactorial n := by
    intro N hnN hN
    have h := Nat.pow_sub_le_descFactorial N n
    have hcast : ((N + 1 - n : ℕ) : ℝ) = N + 1 - n := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [div_pow, div_eq_inv_mul, inv_pow, ← hcast]
    gcongr
    exact_mod_cast h
  have hlim : Tendsto (fun N : ℕ => 2 * (1 - ((N + 1 - n : ℝ) / N) ^ n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ((N + 1 - n : ℝ) / N)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun N : ℕ => 1 + (1 - n : ℝ) / N) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
      rw [add_zero] at h2
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      field_simp
      ring
    have h3 := (h1.pow n).const_sub 1
    simpa using h3.const_mul 2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (max n 1)] with N hN
  have hnN : n ≤ N := le_of_max_le_left hN
  have hN : 0 < N := le_of_max_le_right hN
  rw [Real.norm_eq_abs]
  refine (key N hN).trans ?_
  have := hlow N hnN hN
  linarith

/-! ### The frequencies converge in mean -/

/-- **Second moments under exchangeability**: `E[Xᵢ Xⱼ]` is `P(X₀ = 1)` if `i = j` and
`P(X₀ = X₁ = 1)` otherwise (with `Xᵢ` read as `0/1`). -/
theorem InfExchangeable.integral_toNat_mul_toNat {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} [IsFiniteMeasure P] (hE : InfExchangeable X P) (i j : ℕ) :
    ∫ ω, ((X i ω).toNat : ℝ) * ((X j ω).toNat : ℝ) ∂P =
      if i = j then P.real {ω | ∀ k : Fin 1, X k ω = sortedPattern 1 1 k}
      else P.real {ω | ∀ k : Fin 2, X k ω = sortedPattern 2 2 k} := by
  split_ifs with hij
  · subst hij
    set τ : Fin 1 → Fin (i + 1) := fun _ => ⟨i, by omega⟩
    have hτ : Injective τ := fun a b _ => Subsingleton.elim a b
    have hpt : ∀ ω, ((X i ω).toNat : ℝ) * ((X i ω).toNat : ℝ) =
        ∏ k : Fin 1, (if X (τ k) ω = sortedPattern 1 1 k then (1 : ℝ) else 0) := fun ω => by
      simp only [Fin.prod_univ_one, τ]
      cases X i ω <;> simp [sortedPattern]
    simp_rw [hpt]
    rw [integral_prod_ite_eq hX, hE.measureReal_pattern_comp_injective hX hτ]
  · set τ : Fin 2 → Fin (i + j + 1) := ![⟨i, by omega⟩, ⟨j, by omega⟩]
    have hτ : Injective τ := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [τ, Fin.ext_iff]
    have hpt : ∀ ω, ((X i ω).toNat : ℝ) * ((X j ω).toNat : ℝ) =
        ∏ k : Fin 2, (if X (τ k) ω = sortedPattern 2 2 k then (1 : ℝ) else 0) := fun ω => by
      have key : ∀ b c : Bool, (b.toNat : ℝ) * (c.toNat : ℝ) =
          (if b = sortedPattern 2 2 0 then (1 : ℝ) else 0) *
            (if c = sortedPattern 2 2 1 then (1 : ℝ) else 0) := by
        intro b c
        cases b <;> cases c <;> simp [sortedPattern]
      simp only [Fin.prod_univ_two, τ, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact key _ _
    simp_rw [hpt]
    rw [integral_prod_ite_eq hX, hE.measureReal_pattern_comp_injective hX hτ]

/-- **The mixed moment of two frequencies**: for `1 ≤ N ≤ M`,
`E[(S_N/N)(S_M/M)] = m₂ + (m₁ - m₂)/M` with `m₁ = P(X₀ = 1)`, `m₂ = P(X₀ = X₁ = 1)`. -/
theorem InfExchangeable.integral_successFreq_mul {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} [IsFiniteMeasure P] (hE : InfExchangeable X P) {N M : ℕ} (hN : 0 < N)
    (hNM : N ≤ M) :
    ∫ ω, successFreq X N ω * successFreq X M ω ∂P =
      P.real {ω | ∀ k : Fin 2, X k ω = sortedPattern 2 2 k} +
        (P.real {ω | ∀ k : Fin 1, X k ω = sortedPattern 1 1 k} -
          P.real {ω | ∀ k : Fin 2, X k ω = sortedPattern 2 2 k}) / M := by
  set m1 := P.real {ω | ∀ k : Fin 1, X k ω = sortedPattern 1 1 k}
  set m2 := P.real {ω | ∀ k : Fin 2, X k ω = sortedPattern 2 2 k}
  have hM : 0 < M := lt_of_lt_of_le hN hNM
  have hpt : ∀ ω, successFreq X N ω * successFreq X M ω = ((N : ℝ)⁻¹ * (M : ℝ)⁻¹) *
      ∑ i : Fin N, ∑ j : Fin M, ((X i ω).toNat : ℝ) * ((X j ω).toNat : ℝ) := fun ω => by
    have := Finset.sum_mul_sum (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin M))
      (fun i => ((X i ω).toNat : ℝ)) (fun j => ((X j ω).toNat : ℝ))
    rw [successFreq_eq_sum_fin, successFreq_eq_sum_fin, ← this]
    ring
  have hint : ∀ (i : Fin N) (j : Fin M),
      Integrable (fun ω => ((X i ω).toNat : ℝ) * ((X j ω).toNat : ℝ)) P := fun i j =>
    Integrable.of_bound ((((measurable_of_finite (fun b : Bool => (b.toNat : ℝ))).comp
      (hX _)).mul ((measurable_of_finite (fun b : Bool => (b.toNat : ℝ))).comp
      (hX _))).aestronglyMeasurable) 1
      (ae_of_all _ fun ω => by
        obtain ⟨h1, h2⟩ := toNat_real_mem (X i ω)
        obtain ⟨h3, h4⟩ := toNat_real_mem (X j ω)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h3)]
        nlinarith)
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    hint i j]
  rw [Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j]
  simp_rw [hE.integral_toNat_mul_toNat hX]
  have hrow : ∀ i : Fin N, ∑ j : Fin M, (if (i : ℕ) = (j : ℕ) then m1 else m2) =
      M * m2 + (m1 - m2) := by
    intro i
    have hsplit : ∀ j : Fin M, (if (i : ℕ) = (j : ℕ) then m1 else m2) =
        m2 + (if Fin.castLE hNM i = j then m1 - m2 else 0) := fun j => by
      have : ((i : ℕ) = (j : ℕ)) ↔ Fin.castLE hNM i = j := by simp [Fin.ext_iff]
      by_cases h : Fin.castLE hNM i = j
      · rw [ite_eq_left (this.2 h), ite_eq_left h]; ring
      · rw [ite_eq_right (fun h' => h (this.1 h')), ite_eq_right h]; ring
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_univ _), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

theorem integrable_successFreq_mul {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} [IsFiniteMeasure P] (K L : ℕ) :
    Integrable (fun ω => successFreq X K ω * successFreq X L ω) P :=
  Integrable.of_bound ((measurable_successFreq hX K).mul
    (measurable_successFreq hX L)).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (abs_successFreq_le X K ω) (abs_successFreq_le X L ω) (abs_nonneg _)
        zero_le_one).trans (by norm_num))

/-- **The frequencies are Cauchy in mean square**: for `1 ≤ N ≤ M`,
`E[(S_N/N - S_M/M)²] = (m₁ - m₂)(1/N - 1/M) ≤ 1/N`. -/
theorem InfExchangeable.integral_sq_successFreq_sub_le {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) :
    ∫ ω, (successFreq X N ω - successFreq X M ω) ^ 2 ∂P ≤ 1 / N := by
  have hM : 0 < M := lt_of_lt_of_le hN hNM
  have hbb := integrable_successFreq_mul hX (P := P)
  have hexp : ∀ ω, (successFreq X N ω - successFreq X M ω) ^ 2 =
      successFreq X N ω * successFreq X N ω - 2 * (successFreq X N ω * successFreq X M ω) +
        successFreq X M ω * successFreq X M ω := fun ω => by ring
  simp_rw [hexp]
  rw [integral_add (f := fun ω => successFreq X N ω * successFreq X N ω -
      2 * (successFreq X N ω * successFreq X M ω))
      (g := fun ω => successFreq X M ω * successFreq X M ω)
      ((hbb N N).sub ((hbb N M).const_mul 2)) (hbb M M),
    integral_sub (f := fun ω => successFreq X N ω * successFreq X N ω)
      (g := fun ω => 2 * (successFreq X N ω * successFreq X M ω)) (hbb N N)
      ((hbb N M).const_mul 2), integral_const_mul,
    hE.integral_successFreq_mul hX hN le_rfl, hE.integral_successFreq_mul hX hN hNM,
    hE.integral_successFreq_mul hX hM le_rfl]
  set m1 := P.real {ω | ∀ k : Fin 1, X k ω = sortedPattern 1 1 k}
  set m2 := P.real {ω | ∀ k : Fin 2, X k ω = sortedPattern 2 2 k}
  have hm1 : m1 ≤ 1 := measureReal_le_one
  have hm2 : 0 ≤ m2 := measureReal_nonneg
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hd : 0 ≤ 1 / (N : ℝ) - 1 / M := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hN' hNM'
  have key : m2 + (m1 - m2) / N - 2 * (m2 + (m1 - m2) / M) + (m2 + (m1 - m2) / M) =
      (m1 - m2) * (1 / N - 1 / M) := by
    field_simp
    ring
  rw [key]
  have h1N : 0 ≤ 1 / (M : ℝ) := by positivity
  calc (m1 - m2) * (1 / N - 1 / M) ≤ 1 * (1 / N - 1 / M) :=
        mul_le_mul_of_nonneg_right (by linarith) hd
    _ ≤ 1 / N := by linarith

/-- **The frequencies are Cauchy in mean**: for `1 ≤ N ≤ M`, `E|S_N/N - S_M/M| ≤ 1/√N`. Proof:
`|g| ≤ g²/(2c) + c/2` with `c = 1/√N`, and the mean square bound. -/
theorem InfExchangeable.integral_abs_successFreq_sub_le {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) :
    ∫ ω, |successFreq X N ω - successFreq X M ω| ∂P ≤ 1 / Real.sqrt N := by
  set c : ℝ := 1 / Real.sqrt N with hc
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c := by positivity
  have hc2 : c ^ 2 = 1 / N := by
    rw [hc, div_pow, one_pow, Real.sq_sqrt hN'.le]
  have hpt : ∀ ω, |successFreq X N ω - successFreq X M ω| ≤
      (successFreq X N ω - successFreq X M ω) ^ 2 / (2 * c) + c / 2 := by
    intro ω
    set g := successFreq X N ω - successFreq X M ω
    have h1 : g ^ 2 / (2 * c) + c / 2 = (g ^ 2 + c ^ 2) / (2 * c) := by
      field_simp
    rw [h1, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|g| - c), sq_abs g]
  have hb := abs_successFreq_le X
  have hmeas : Measurable fun ω => successFreq X N ω - successFreq X M ω :=
    (measurable_successFreq hX N).sub (measurable_successFreq hX M)
  have hsq : Integrable (fun ω => (successFreq X N ω - successFreq X M ω) ^ 2) P :=
    Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable 4 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_pow]
      have : |successFreq X N ω - successFreq X M ω| ≤ 2 :=
        (abs_sub _ _).trans (by linarith [hb N ω, hb M ω])
      nlinarith [abs_nonneg (successFreq X N ω - successFreq X M ω)])
  have habs : Integrable (fun ω => |successFreq X N ω - successFreq X M ω|) P :=
    Integrable.of_bound (continuous_abs.measurable.comp hmeas).aestronglyMeasurable 2
      (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_abs]
      exact (abs_sub _ _).trans (by linarith [hb N ω, hb M ω]))
  calc ∫ ω, |successFreq X N ω - successFreq X M ω| ∂P
      ≤ ∫ ω, ((successFreq X N ω - successFreq X M ω) ^ 2 / (2 * c) + c / 2) ∂P :=
        integral_mono habs ((hsq.div_const _).add (integrable_const _)) hpt
    _ = (∫ ω, (successFreq X N ω - successFreq X M ω) ^ 2 ∂P) / (2 * c) + c / 2 := by
        rw [integral_add (hsq.div_const _) (integrable_const _), integral_div]
        simp
    _ ≤ (1 / N) / (2 * c) + c / 2 := by
        gcongr
        exact hE.integral_sq_successFreq_sub_le hX hN hNM
    _ = c := by
        rw [← hc2]
        field_simp
        ring

/-- Clamping to `[0, 1]` does not increase the distance to a point of `[0, 1]`. -/
theorem abs_sub_max_min_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x - max 0 (min 1 y)| ≤ |x - y| := by
  rcases le_total 1 y with h | h
  · rw [min_eq_left h, max_eq_right zero_le_one, abs_sub_comm x 1, abs_sub_comm x y,
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [min_eq_right h]
    rcases le_total 0 y with h' | h'
    · rw [max_eq_right h']
    · rw [max_eq_left h', sub_zero, abs_of_nonneg hx0, abs_of_nonneg (by linarith : 0 ≤ x - y)]
      linarith

/-- **The frequency of successes converges in mean**: for an infinitely exchangeable binary
sequence there is a measurable `Θ` with values in `[0, 1]` and `E|S_N/N - Θ| → 0`. Proof: by the
bound `E|S_N/N - S_M/M| ≤ 1/√N` the frequencies are Cauchy in the complete space `L¹(P)`;
clamping a representative of the limit to `[0, 1]` only brings it closer to each frequency. -/
theorem InfExchangeable.exists_tendsto_integral_abs_successFreq {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) :
    ∃ Θ : Ω → ℝ, Measurable Θ ∧ (∀ ω, Θ ω ∈ Icc (0 : ℝ) 1) ∧
      Tendsto (fun N => ∫ ω, |successFreq X N ω - Θ ω| ∂P) atTop (𝓝 0) := by
  have hb := abs_successFreq_le X
  have hm : ∀ K, MemLp (successFreq X K) 1 P := fun K =>
    MemLp.of_bound (measurable_successFreq hX K).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb K ω)
  let u : ℕ → Lp ℝ 1 P := fun k => (hm (k + 1)).toLp _
  have hdist : ∀ k (G : Lp ℝ 1 P), dist (u k) G = ∫ ω, |successFreq X (k + 1) ω - G ω| ∂P := by
    intro k G
    rw [L1.dist_eq_integral_dist]
    refine integral_congr_ae ?_
    filter_upwards [(hm (k + 1)).coeFn_toLp] with ω hω
    simp only [u, hω, Real.dist_eq]
  have hcs : CauchySeq u := by
    refine cauchySeq_of_le_tendsto_0' (fun k : ℕ => 1 / Real.sqrt (k + 1)) (fun a b hab => ?_) ?_
    · rw [L1.dist_eq_integral_dist]
      have h := hE.integral_abs_successFreq_sub_le hX (Nat.succ_pos a) (Nat.succ_le_succ hab)
      push_cast at h
      refine le_of_eq_of_le (integral_congr_ae ?_) h
      filter_upwards [(hm (a + 1)).coeFn_toLp, (hm (b + 1)).coeFn_toLp] with ω h1 h2
      simp only [u, h1, h2, Real.dist_eq]
    · have h1 : Tendsto (fun k : ℕ => Real.sqrt (k + 1)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1
          tendsto_natCast_atTop_atTop)
      exact h1.inv_tendsto_atTop.congr fun k => by simp
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcs
  have hFm : Measurable (F : Ω → ℝ) := (Lp.stronglyMeasurable F).measurable
  refine ⟨fun ω => max 0 (min 1 (F ω)), by fun_prop,
    fun ω => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, ?_⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  have hdF : Tendsto (fun k => dist (u k) F) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.1 hF
  refine squeeze_zero (fun k => integral_nonneg fun ω => abs_nonneg _) (fun k => ?_) hdF
  rw [hdist]
  have hFi : Integrable (fun ω => |successFreq X (k + 1) ω - F ω|) P :=
    (((hm (k + 1)).integrable le_rfl).sub (L1.integrable_coeFn F)).abs
  refine integral_mono (Integrable.of_bound
    (Measurable.aestronglyMeasurable (by have := measurable_successFreq hX (k + 1); fun_prop))
    2 (ae_of_all _ fun ω => ?_)) hFi fun ω => ?_
  · rw [Real.norm_eq_abs, abs_abs]
    refine (abs_sub _ _).trans ?_
    have h1 := hb (k + 1) ω
    have h2 : |max 0 (min 1 (F ω))| ≤ 1 := by
      rw [abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (min_le_left _ _)
    linarith
  · obtain ⟨h1, h2⟩ := successFreq_mem_Icc X (k + 1) ω
    exact abs_sub_max_min_le h1 h2

/-! ### Moments of the limit -/

/-- The product rule bound `|xA - yB| ≤ |x - y| + |A - B|` for `|A|, |y| ≤ 1`. -/
theorem abs_mul_sub_mul_le_of_abs_le_one {x y A B : ℝ} (hA : |A| ≤ 1) (hy : |y| ≤ 1) :
    |x * A - y * B| ≤ |x - y| + |A - B| := by
  have h : x * A - y * B = (x - y) * A + y * (A - B) := by ring
  rw [h]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  gcongr
  · exact mul_le_of_le_one_right (abs_nonneg _) hA
  · exact mul_le_of_le_one_left (abs_nonneg _) hy

/-- `|uᵃ - vᵃ| ≤ a |u - v|` on `[0, 1]`. -/
theorem abs_pow_sub_pow_le_mul_of_mem_Icc {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (a : ℕ) : |u ^ a - v ^ a| ≤ a * |u - v| := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', pow_succ']
    have hA : |u ^ a| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hu.1 _)]
      exact pow_le_one₀ hu.1 hu.2
    have hy : |v| ≤ 1 := by rw [abs_of_nonneg hv.1]; exact hv.2
    refine (abs_mul_sub_mul_le_of_abs_le_one hA hy).trans ?_
    push_cast
    linarith

/-- **Lipschitz bound for the Bernstein monomial**: on `[0, 1]`,
`|uᵃ(1-u)ᵇ - vᵃ(1-v)ᵇ| ≤ (a + b) |u - v|`. -/
theorem abs_bernstein_sub_bernstein_le {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (a b : ℕ) :
    |u ^ a * (1 - u) ^ b - v ^ a * (1 - v) ^ b| ≤ (a + b) * |u - v| := by
  have hu' : 1 - u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hv' : 1 - v ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hv.2], by linarith [hv.1]⟩
  have hA : |(1 - u) ^ b| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hu'.1 _)]
    exact pow_le_one₀ hu'.1 hu'.2
  have hy : |v ^ a| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hv.1 _)]
    exact pow_le_one₀ hv.1 hv.2
  refine (abs_mul_sub_mul_le_of_abs_le_one hA hy).trans ?_
  have h1 := abs_pow_sub_pow_le_mul_of_mem_Icc hu hv a
  have h2 := abs_pow_sub_pow_le_mul_of_mem_Icc hu' hv' b
  have h3 : |(1 - u) - (1 - v)| = |u - v| := by
    rw [show (1 - u) - (1 - v) = -(u - v) by ring, abs_neg]
  rw [h3] at h2
  linarith

/-- The Bernstein monomial `θᵃ (1 - θ)ᵇ` lies in `[0, 1]` on `[0, 1]`. -/
theorem bernstein_mem_Icc {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (a b : ℕ) :
    θ ^ a * (1 - θ) ^ b ∈ Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ 1 - θ := by linarith [hθ.2]
  refine ⟨mul_nonneg (pow_nonneg hθ.1 _) (pow_nonneg h0 _), ?_⟩
  exact (mul_le_mul (pow_le_one₀ hθ.1 hθ.2) (pow_le_one₀ h0 (by linarith [hθ.1]))
    (pow_nonneg h0 _) zero_le_one).trans (by norm_num)

/-- **Moments of the limit frequency**: if `E|S_N/N - Θ| → 0` with `Θ` measurable with values in
`[0, 1]`, then for `a ≤ n`, `E[Θᵃ (1 - Θ)^{n-a}]` is the probability of the sorted pattern with
`a` successes. Proof: by the Lipschitz bound the moments of `S_N/N` converge to those of `Θ`, and
they converge to the pattern probability. -/
theorem InfExchangeable.integral_bernstein_limit {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} [IsProbabilityMeasure P] (hE : InfExchangeable X P) {Θ : Ω → ℝ}
    (hΘm : Measurable Θ) (hΘ : ∀ ω, Θ ω ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto (fun N => ∫ ω, |successFreq X N ω - Θ ω| ∂P) atTop (𝓝 0)) {a n : ℕ}
    (han : a ≤ n) :
    ∫ ω, Θ ω ^ a * (1 - Θ ω) ^ (n - a) ∂P =
      P.real {ω | ∀ j : Fin n, X j ω = sortedPattern a n j} := by
  refine tendsto_nhds_unique ?_ (hE.tendsto_integral_successFreq_bernstein hX han)
  have hgm : ∀ f : Ω → ℝ, Measurable f → (∀ ω, f ω ∈ Icc (0 : ℝ) 1) →
      Integrable (fun ω => f ω ^ a * (1 - f ω) ^ (n - a)) P := fun f hf hf01 =>
    Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 1
      (ae_of_all _ fun ω => by
        obtain ⟨h1, h2⟩ := bernstein_mem_Icc (hf01 ω) a (n - a)
        rw [Real.norm_eq_abs, abs_of_nonneg h1]
        exact h2)
  have hfr : ∀ N ω, successFreq X N ω ∈ Icc (0 : ℝ) 1 := successFreq_mem_Icc X
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) ((hlim.const_mul (n : ℝ)).trans
    (by rw [mul_zero]))
  rw [Real.norm_eq_abs, ← integral_sub (hgm _ (measurable_successFreq hX N) (hfr N))
    (hgm _ hΘm hΘ)]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) ?_
    (ae_of_all _ fun ω => ?_)
  · refine Integrable.const_mul (Integrable.of_bound (continuous_abs.measurable.comp
      ((measurable_successFreq hX N).sub hΘm)).aestronglyMeasurable 2
      (ae_of_all _ fun ω => ?_)) _
    simp only [Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply, abs_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (hfr N ω).1, abs_of_nonneg (hΘ ω).1]
    linarith [(hfr N ω).2, (hΘ ω).2]
  · have h := abs_bernstein_sub_bernstein_le (hfr N ω) (hΘ ω) a (n - a)
    have hc : (a : ℝ) + ((n - a : ℕ) : ℝ) = n := by
      rw [Nat.cast_sub han]
      ring
    rw [hc] at h
    exact h

/-! ### The theorem -/

/-- The law of a measurable `Θ` with values in `[0, 1]` gives no mass to the complement of
`[0, 1]`. -/
theorem map_compl_Icc_eq_zero {P : Measure Ω} {Θ : Ω → ℝ} (hΘm : Measurable Θ)
    (hΘ : ∀ ω, Θ ω ∈ Icc (0 : ℝ) 1) : P.map Θ (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [Measure.map_apply hΘm measurableSet_Icc.compl]
  have : Θ ⁻¹' (Icc (0 : ℝ) 1)ᶜ = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
      not_not]
    exact hΘ ω
  rw [this, measure_empty]

/-- The pattern probabilities of an infinitely exchangeable binary sequence are the Bernstein
moments of the law of the limit in mean of the frequencies. -/
theorem InfExchangeable.measureReal_pattern_eq_integral_map {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P]
    (hE : InfExchangeable X P) {Θ : Ω → ℝ} (hΘm : Measurable Θ) (hΘ : ∀ ω, Θ ω ∈ Icc (0 : ℝ) 1)
    (hlim : Tendsto (fun N => ∫ ω, |successFreq X N ω - Θ ω| ∂P) atTop (𝓝 0)) {n : ℕ}
    (x : Fin n → Bool) :
    P.real {ω | ∀ j : Fin n, X j ω = x j} =
      ∫ θ, θ ^ boolCount x * (1 - θ) ^ (n - boolCount x) ∂(P.map Θ) := by
  rw [integral_map hΘm.aemeasurable (by fun_prop), hE.measureReal_pattern_eq_sorted hX,
    hE.integral_bernstein_limit hX hΘm hΘ hlim (boolCount_le x)]

/-- The real form of a pattern probability as a Bernstein moment converts to the form with a
lower integral used by `infExchangeable_of_binary_mixture`. -/
theorem measure_eq_lintegral_of_measureReal_eq_integral {P : Measure Ω} [IsFiniteMeasure P]
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hμ : μ (Icc (0 : ℝ) 1)ᶜ = 0) {A : Set Ω} {a b : ℕ}
    (h : P.real A = ∫ θ, θ ^ a * (1 - θ) ^ b ∂μ) :
    P A = ∫⁻ θ, ENNReal.ofReal (θ ^ a * (1 - θ) ^ b) ∂μ := by
  have hae : ∀ᵐ θ ∂μ, θ ∈ Icc (0 : ℝ) 1 := mem_ae_iff.2 hμ
  rw [← ofReal_integral_eq_lintegral_ofReal, ← h, ofReal_measureReal (measure_ne_top _ _)]
  · refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [hae] with θ hθ
    obtain ⟨h1, h2⟩ := bernstein_mem_Icc hθ a b
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact h2
  · filter_upwards [hae] with θ hθ
    exact (bernstein_mem_Icc hθ a b).1

/-- **de Finetti's theorem for binary sequences, existence** (de Finetti 1937): for an infinitely
exchangeable sequence of measurable `Bool` valued variables there is a probability measure `Π`
on `ℝ` with `Π([0, 1]ᶜ) = 0` such that for every `n` and every pattern `x` with `s` successes
`P(X₀ = x₀, …, X_{n-1} = x_{n-1}) = ∫ θ^s (1 - θ)^{n-s} dΠ(θ)`. The measure `Π` is the law of the
limit in mean of the frequencies `S_N / N`. -/
theorem InfExchangeable.exists_binaryMixture {X : ℕ → Ω → Bool} (hX : ∀ i, Measurable (X i))
    {P : Measure Ω} [IsProbabilityMeasure P] (hE : InfExchangeable X P) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ (n : ℕ) (x : Fin n → Bool), P {ω | ∀ i : Fin n, X i ω = x i} =
        ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂μ := by
  obtain ⟨Θ, hΘm, hΘ, hlim⟩ := hE.exists_tendsto_integral_abs_successFreq hX
  have hprob : IsProbabilityMeasure (P.map Θ) :=
    (Measure.isProbabilityMeasure_map_iff hΘm.aemeasurable).2 inferInstance
  have hsupp := map_compl_Icc_eq_zero (P := P) hΘm hΘ
  exact ⟨P.map Θ, hprob, hsupp, fun n x => measure_eq_lintegral_of_measureReal_eq_integral hsupp
    (hE.measureReal_pattern_eq_integral_map hX hΘm hΘ hlim x)⟩

/-- **de Finetti's characterization of infinitely exchangeable binary sequences**: a sequence of
measurable `Bool` valued variables on a probability space is infinitely exchangeable if and only
if there is a probability measure `Π` on `[0, 1]` with
`P(X₀ = x₀, …, X_{n-1} = x_{n-1}) = ∫ θ^s (1 - θ)^{n-s} dΠ(θ)` for every pattern. -/
theorem infExchangeable_iff_exists_binaryMixture {X : ℕ → Ω → Bool}
    (hX : ∀ i, Measurable (X i)) {P : Measure Ω} [IsProbabilityMeasure P] :
    InfExchangeable X P ↔ ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ (n : ℕ) (x : Fin n → Bool), P {ω | ∀ i : Fin n, X i ω = x i} =
        ∫⁻ θ, ENNReal.ofReal (θ ^ boolCount x * (1 - θ) ^ (n - boolCount x)) ∂μ :=
  ⟨fun hE => hE.exists_binaryMixture hX, fun ⟨_, _, _, h⟩ =>
    infExchangeable_of_binary_mixture hX h⟩

end MetaAnalysis

end CausalInference
