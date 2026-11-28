/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapOrder

/-!
# Conditional Chebyshev bounds for resample means

Given the data, the resampled observations are independent with the empirical law of the first
`n` observations. The resample mean `ḡ*ₙ = n⁻¹ ∑ᵢ g(yᵢ)` therefore has conditional mean
`ḡₙ = sampleMean g` and conditional variance at most `n⁻¹ (g²)‾ₙ`, and Chebyshev's inequality gives
`P*(|ḡ*ₙ - ḡₙ| ≥ ε) ≤ (g²)‾ₙ / (n ε²)` at every data point
(`resampleLaw_le_abs_resampleMean_sub_le`). With the law of large numbers for `g²` this gives the
bootstrap law of large numbers and the `√n` bound in conditional probability, in probability, for
every `g` with `E g(O_0)² < ∞`.

## Main results

* `resampleLaw_le_abs_resampleMean_sub_le`: the conditional Chebyshev bound.
* `resampleTendstoZero_resampleMean_sub_integral`: `ḡ*ₙ → E g(O_0)` in conditional probability, in
  probability.
* `resampleBounded_sqrt_mul_resampleMean_sub_integral`: `√n (ḡ*ₙ - E g(O_0))` is bounded in
  conditional probability, in probability.
* `resampleMean_add`, `resampleMean_sub`, `resampleMean_const_mul`, `resampleMean_sum`,
  `abs_resampleMean_le`: the resample mean is linear and monotone.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* P. J. Bickel and D. A. Freedman (1981), *Some asymptotic theory for the bootstrap*, Annals of
  Statistics 9.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open Bootstrap

/-! ### Linearity of the resample mean -/

section Linear

variable {𝒪 : Type*} {n : ℕ} (y : Fin n → 𝒪)

theorem resampleMean_add (f g : 𝒪 → ℝ) :
    resampleMean (fun z => f z + g z) n y = resampleMean f n y + resampleMean g n y := by
  simp [resampleMean, Finset.sum_add_distrib, mul_add]

theorem resampleMean_sub (f g : 𝒪 → ℝ) :
    resampleMean (fun z => f z - g z) n y = resampleMean f n y - resampleMean g n y := by
  simp [resampleMean, Finset.sum_sub_distrib, mul_sub]

theorem resampleMean_const_mul (c : ℝ) (f : 𝒪 → ℝ) :
    resampleMean (fun z => c * f z) n y = c * resampleMean f n y := by
  simp only [resampleMean, ← Finset.mul_sum]
  ring

theorem resampleMean_sum {ι : Type*} (s : Finset ι) (f : ι → 𝒪 → ℝ) :
    resampleMean (fun z => ∑ i ∈ s, f i z) n y = ∑ i ∈ s, resampleMean (f i) n y := by
  simp only [resampleMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem resampleMean_const (hn : 0 < n) (c : ℝ) : resampleMean (fun _ : 𝒪 => c) n y = c := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [resampleMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Monotonicity**: if `|f(yᵢ)| ≤ g(yᵢ)` for every `i`, then `|ḡ*_f| ≤ ḡ*_g`. -/
theorem abs_resampleMean_le {f g : 𝒪 → ℝ} (h : ∀ i, |f (y i)| ≤ g (y i)) :
    |resampleMean f n y| ≤ resampleMean g n y := by
  simp only [resampleMean]
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => h i)) (by positivity)

theorem resampleMean_nonneg {f : 𝒪 → ℝ} (h : ∀ i, 0 ≤ f (y i)) : 0 ≤ resampleMean f n y := by
  simp only [resampleMean]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => h i)

end Linear

/-! ### The conditional Chebyshev bound -/

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-- **Conditional Chebyshev bound.** For a measurable `g`, `n > 0` and `ε > 0`, at every data point
`P*(|ḡ*ₙ - ḡₙ| ≥ ε) ≤ (g²)‾ₙ / (n ε²)`, with `ḡₙ` and `(g²)‾ₙ` the sample means of `g` and `g²`. -/
theorem resampleLaw_le_abs_resampleMean_sub_le {g : 𝒪 → ℝ} (hg : Measurable g)
    (O : ℕ → Ω → 𝒪) {n : ℕ} (hn : 0 < n) (ω : Ω) {ε : ℝ} (hε : 0 < ε) :
    resampleLaw O n ω {y | ε ≤ |resampleMean g n y - sampleMean g O n ω|} ≤
      ENNReal.ofReal (sampleMean (fun z => g z ^ 2) O n ω / (n * ε ^ 2)) := by
  set Q := resampleLaw O n ω
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL2 : ∀ i : Fin n, MemLp (fun y : Fin n → 𝒪 => g (y i)) 2 Q := fun i =>
    memLp_comp_eval_resampleLaw hg.stronglyMeasurable O n ω i
  have hX : MemLp (fun y => resampleMean g n y) 2 Q :=
    (memLp_finsetSum _ fun i _ => hL2 i).const_mul _
  have hmean : Q[fun y => resampleMean g n y] = sampleMean g O n ω := by
    simp only [resampleMean]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => (hL2 i).integrable one_le_two]
    rw [Finset.sum_congr rfl fun i _ => integral_comp_eval_resampleLaw hg O n ω i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hsum : Var[fun y : Fin n → 𝒪 => ∑ i, g (y i); Q] = ∑ i, Var[fun y => g (y i); Q] := by
    have hfn : (fun y : Fin n → 𝒪 => ∑ i, g (y i)) = ∑ i, fun y => g (y i) := by
      ext y; simp only [Finset.sum_apply]
    rw [hfn, IndepFun.variance_sum (fun i _ => hL2 i)
      fun i _ j _ hij => ((iIndepFun_resampleLaw O n ω).indepFun hij).comp hg hg]
  have hle : ∀ i, Var[fun y : Fin n → 𝒪 => g (y i); Q] ≤ sampleMean (fun z => g z ^ 2) O n ω :=
    fun i => by
      refine (variance_le_expectation_sq (hL2 i).aestronglyMeasurable).trans_eq ?_
      rw [← integral_comp_eval_resampleLaw (hg.pow_const 2) O n ω i]
      rfl
  have hvar : Var[fun y => resampleMean g n y; Q] ≤ sampleMean (fun z => g z ^ 2) O n ω / n := by
    simp only [resampleMean]
    rw [variance_const_mul, hsum]
    calc ((n : ℝ)⁻¹) ^ 2 * ∑ i, Var[fun y : Fin n → 𝒪 => g (y i); Q]
        ≤ ((n : ℝ)⁻¹) ^ 2 * ∑ _i : Fin n, sampleMean (fun z => g z ^ 2) O n ω :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hle i) (by positivity)
      _ = sampleMean (fun z => g z ^ 2) O n ω / n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have h := meas_ge_le_variance_div_sq hX hε
  rw [hmean] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right hvar (by positivity : (0 : ℝ) ≤ n * ε ^ 2)
  calc _ ≤ _ := this
    _ = sampleMean (fun z => g z ^ 2) O n ω * ε ^ 2 := by field_simp

/-! ### Laws of large numbers in conditional probability -/

variable {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪}

omit [IsProbabilityMeasure P] in
theorem memLp_comp_of_map (hO : IsIIDSample O P) {g : 𝒪 → ℝ} (hg : Measurable g)
    (hg2 : MemLp g 2 (P.map (O 0))) : MemLp (fun ω => g (O 0 ω)) 2 P :=
  (memLp_map_measure_iff hg.aestronglyMeasurable (hO.aemeasurable 0)).1 hg2

omit [IsProbabilityMeasure P] in
theorem integral_comp_of_map (hO : IsIIDSample O P) {g : 𝒪 → ℝ} (hg : Measurable g) :
    P[fun ω => g (O 0 ω)] = ∫ z, g z ∂(P.map (O 0)) :=
  (integral_map (hO.aemeasurable 0) hg.aestronglyMeasurable).symm

/-- The sample mean of `g²` is below `E g(O_0)² + 1` with probability tending to one. -/
theorem withProbTendingToOne_sampleMean_sq_lt (hO : IsIIDSample O P) {g : 𝒪 → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 (P.map (O 0))) :
    WithProbTendingToOne P fun n => {ω | sampleMean (fun z => g z ^ 2) O n ω <
      ∫ z, g z ^ 2 ∂(P.map (O 0)) + 1} := by
  have hint : Integrable (fun ω => g (O 0 ω) ^ 2) P := (memLp_comp_of_map hO hg hg2).integrable_sq
  have h := (hO.tendstoInMeasure_smul_sum (f := fun z => g z ^ 2) (hg.pow_const 2) hint)
    |>.withProbTendingToOne_dist_lt one_pos
  rw [integral_comp_of_map hO (hg.pow_const 2)] at h
  refine h.mono fun n ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq, smul_eq_mul] at hω ⊢
  have := (abs_lt.1 hω).2
  simp only [sampleMean]
  linarith

/-- **The bootstrap law of large numbers about the data**: for `g` measurable with
`E g(O_0)² < ∞`, `ḡ*ₙ - ḡₙ → 0` in conditional probability, in probability. -/
theorem resampleTendstoZero_resampleMean_sub_sampleMean (hO : IsIIDSample O P) {g : 𝒪 → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 (P.map (O 0))) :
    ResampleTendstoZero P O fun n ω y => resampleMean g n y - sampleMean g O n ω := by
  intro ε hε κ hκ
  set S := ∫ z, g z ^ 2 ∂(P.map (O 0)) + 1 with hS
  have hS0 : 0 < S := by
    have : 0 ≤ ∫ z, g z ^ 2 ∂(P.map (O 0)) := integral_nonneg fun _ => sq_nonneg _
    linarith
  have hA := (withProbTendingToOne_sampleMean_sq_lt hO hg hg2).eventually_le
    (ENNReal.ofReal_pos.2 hκ)
  have hC := (tendsto_const_div_atTop_nhds_zero_nat (S / ε ^ 2)).eventually (gt_mem_nhds hκ)
  filter_upwards [hA, hC, eventually_ge_atTop 1] with n hnA hnC hn1
  refine (measure_mono fun ω hω => ?_).trans hnA
  intro hωA
  simp only [Set.mem_ofPred_eq, not_lt] at hω hωA
  have hb := resampleLaw_le_abs_resampleMean_sub_le hg O hn1 ω hε
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hreal := ENNReal.toReal_le_of_le_ofReal (by
    have : 0 ≤ sampleMean (fun z => g z ^ 2) O n ω := by
      simp only [sampleMean]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    positivity) hb
  have h2 : sampleMean (fun z => g z ^ 2) O n ω / (n * ε ^ 2) < κ := by
    calc sampleMean (fun z => g z ^ 2) O n ω / (n * ε ^ 2) ≤ S / (n * ε ^ 2) :=
          div_le_div_of_nonneg_right hωA.le (by positivity)
      _ = S / ε ^ 2 / n := by rw [div_div, mul_comm]
      _ < κ := hnC
  change κ ≤ ((resampleLaw O n ω) _).toReal at hω
  linarith

/-- **The bootstrap law of large numbers**: for `g` measurable with `E g(O_0)² < ∞`,
`ḡ*ₙ → E g(O_0)` in conditional probability, in probability. -/
theorem resampleTendstoZero_resampleMean_sub_integral (hO : IsIIDSample O P) {g : 𝒪 → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 (P.map (O 0))) :
    ResampleTendstoZero P O fun n _ y => resampleMean g n y - ∫ z, g z ∂(P.map (O 0)) := by
  have hint : Integrable (fun ω => g (O 0 ω)) P :=
    (memLp_comp_of_map hO hg hg2).integrable one_le_two
  have h := ResampleTendstoZero.of_tendstoInMeasure (O := O)
    (hO.tendstoInMeasure_smul_sum hg hint)
  rw [integral_comp_of_map hO hg] at h
  refine ((resampleTendstoZero_resampleMean_sub_sampleMean hO hg hg2).add h).of_le
    (ResampleEventually.of_eventually (Eventually.of_forall fun n ω y => le_of_eq ?_))
  simp only [smul_eq_mul, sampleMean]
  ring_nf

/-- **The `√n` bound in conditional probability**: for `g` measurable with `E g(O_0)² < ∞`,
`√n (ḡ*ₙ - ḡₙ)` is bounded in conditional probability, in probability. -/
theorem resampleBounded_sqrt_mul_resampleMean_sub_sampleMean (hO : IsIIDSample O P)
    {g : 𝒪 → ℝ} (hg : Measurable g) (hg2 : MemLp g 2 (P.map (O 0))) :
    ResampleBounded P O fun n ω y => √(n : ℝ) * (resampleMean g n y - sampleMean g O n ω) := by
  intro κ hκ
  set S := ∫ z, g z ^ 2 ∂(P.map (O 0)) + 1 with hS
  have hS0 : 0 < S := by
    have : 0 ≤ ∫ z, g z ^ 2 ∂(P.map (O 0)) := integral_nonneg fun _ => sq_nonneg _
    linarith
  set K := √(S / κ) + 1 with hK
  have hK0 : 0 < K := by positivity
  have hKS : S / K ^ 2 < κ := by
    have h1 : √(S / κ) ^ 2 = S / κ := Real.sq_sqrt (by positivity)
    have h2 : S / κ < K ^ 2 := by rw [hK]; nlinarith [Real.sqrt_nonneg (S / κ)]
    rw [div_lt_iff₀ (by positivity)]
    rwa [div_lt_iff₀ hκ, mul_comm] at h2
  refine ⟨K, ?_⟩
  have hA := (withProbTendingToOne_sampleMean_sq_lt hO hg hg2).eventually_le
    (ENNReal.ofReal_pos.2 hκ)
  filter_upwards [hA, eventually_ge_atTop 1] with n hnA hn1
  refine (measure_mono fun ω hω => ?_).trans hnA
  intro hωA
  simp only [Set.mem_ofPred_eq] at hω hωA
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnR
  have hb := resampleLaw_le_abs_resampleMean_sub_le hg O hn1 ω (div_pos hK0 hsq)
  have hsub : {y | ¬ |√(n : ℝ) * (resampleMean g n y - sampleMean g O n ω)| ≤ K} ⊆
      {y | K / √(n : ℝ) ≤ |resampleMean g n y - sampleMean g O n ω|} := by
    intro y hy
    simp only [Set.mem_ofPred_eq, not_le, abs_mul, abs_of_pos hsq] at hy ⊢
    rw [div_le_iff₀ hsq, mul_comm]
    exact hy.le
  have h0 : 0 ≤ sampleMean (fun z => g z ^ 2) O n ω := by
    simp only [sampleMean]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hreal := ENNReal.toReal_le_of_le_ofReal (by positivity) ((measure_mono hsub).trans hb)
  have hn2 : (n : ℝ) * (K / √(n : ℝ)) ^ 2 = K ^ 2 := by
    rw [div_pow, Real.sq_sqrt hnR.le]
    field_simp
  rw [hn2] at hreal
  have h2 : sampleMean (fun z => g z ^ 2) O n ω / K ^ 2 < κ :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right hωA.le (by positivity)) hKS
  change κ ≤ ((resampleLaw O n ω) _).toReal at hω
  linarith

/-- **The `√n` bound about the population mean**: for `g` measurable with `E g(O_0)² < ∞`,
`√n (ḡ*ₙ - E g(O_0))` is bounded in conditional probability, in probability. -/
theorem resampleBounded_sqrt_mul_resampleMean_sub_integral (hO : IsIIDSample O P)
    {g : 𝒪 → ℝ} (hg : Measurable g) (hg2 : MemLp g 2 (P.map (O 0))) :
    ResampleBounded P O fun n _ y => √(n : ℝ) * (resampleMean g n y - ∫ z, g z ∂(P.map (O 0))) := by
  have hAL := sampleMean_isAsymptoticallyLinear hg (memLp_comp_of_map hO hg hg2)
  have hD := ResampleBounded.of_data (O := O) (hAL.sqrt_mul_sub_boundedInProbability hO)
  rw [integral_comp_of_map hO hg] at hD
  refine ((resampleBounded_sqrt_mul_resampleMean_sub_sampleMean hO hg hg2).add hD).of_le
    (ResampleEventually.of_eventually (Eventually.of_forall fun n ω y => le_of_eq ?_))
  ring_nf

end PopulationAdjustment

end CausalInference
