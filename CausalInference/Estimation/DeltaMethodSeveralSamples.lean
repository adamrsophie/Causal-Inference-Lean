/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.DeltaMethodMultivariate
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.CentralLimitTheorem

/-!
# The delta method for independent samples of different sizes

Estimates from independent studies of different sizes (a validation study and a main study,
cases and controls, the studies of a meta-analysis) are modeled here by one i.i.d. sample
`O i : ℕ → Ω → 𝒪 i` per study `i` of a finite index type, the samples mutually independent as
sequences (`iIndepFun (fun i ω ↦ fun j ↦ O i j ω) μ`), and a sample size `N i n` for study `i`
with `N i n / n → rᵢ > 0`. The estimator of study `i` is asymptotically linear in its own sample,
in the sense of `IsAsymptoticallyLinear`, and is evaluated at its own size `N i n`.

* `tendstoInDistribution_sum_normalizedSum`: joint central limit theorem. For independent
  samples and any sizes `N i n → ∞`, `∑ᵢ aᵢ (N i n)^{-1/2} ∑_{j < N i n} φᵢ (O i j)` converges in
  distribution to the centered Gaussian with variance `∑ᵢ aᵢ² E φᵢ²`. The proof goes through
  characteristic functions (Lévy's continuity theorem): independence factors the characteristic
  function of the sum, and each factor converges by the central limit theorem along `N i n`.
* `IsAsymptoticallyLinear.sqrt_mul_sub_sub_normalizedSum`: the Slutsky step for one study,
  `√n (θhat (N n) - θ) - r^{-1/2} (N n)^{-1/2} ∑_{j < N n} φ (O j) → 0` in probability, and
  `IsAsymptoticallyLinear.boundedInProbability_of_sizes`: `√n (θhat (N n) - θ)` is bounded in
  probability (`BoundedInProbability`).
* `tendstoInMeasure_sqrt_mul_comp_sub_sum`: the deterministic part of the delta method along
  arbitrary sequences (`T i n → θ i` in probability with `√n (T i n - θ i)` bounded).
* `tendstoInDistribution_comp_hasFDerivAt_of_sizes`: **the delta method for several samples.**
  For `g` with Fréchet derivative `L` at `θ`, `√n (g (θhat · (N · n)) - g θ)` converges in
  distribution to the centered Gaussian with variance `∑ᵢ L(eᵢ)² E φᵢ² / rᵢ`.

The assumptions of the final theorem are exactly: a probability measure; each `O i` i.i.d.; the
samples mutually independent; each `θhat i` asymptotically linear at `θ i` with influence
function `φ i` in `O i`; `N i n / n → rᵢ > 0`; `g` Fréchet differentiable at `θ`; and the final
statistic almost everywhere measurable for every `n`. The estimators need not be functions of
their own samples: only their linear parts are, and the remainders are controlled in probability.

Source: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapters 2 and 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Complex
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The normalized sum `m^{-1/2} ∑_{j < m} φ (O j)` of the first `m` observations. -/
noncomputable def normalizedSum {𝒪 : Type*} (φ : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (m : ℕ) (ω : Ω) : ℝ :=
  (√(m : ℝ))⁻¹ * ∑ j ∈ range m, φ (O j ω)

/-- **Central limit theorem through characteristic functions.** For an i.i.d. sample and a
centered square integrable `φ (O 0)`, the characteristic function of the normalized sum at `s`
converges to that of `N(0, E φ (O 0)²)`. -/
theorem tendsto_charFun_normalizedSum {𝒪 : Type*} [MeasurableSpace 𝒪] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {φ : 𝒪 → ℝ}
    (hφ : Measurable φ) (h2 : MemLp (fun ω ↦ φ (O 0 ω)) 2 μ) (h0 : μ[fun ω ↦ φ (O 0 ω)] = 0)
    (s : ℝ) :
    Tendsto (fun m ↦ charFun (μ.map (normalizedSum φ O m)) s) atTop
      (𝓝 (charFun (gaussianReal 0 (μ[fun ω ↦ φ (O 0 ω) ^ 2]).toNNReal) s)) := by
  have hX := hO.comp hφ
  have hvar : Var[fun ω ↦ φ (O 0 ω); μ] = μ[fun ω ↦ φ (O 0 ω) ^ 2] :=
    variance_of_integral_eq_zero h2.aemeasurable h0
  have hY : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (Var[fun ω ↦ φ (O 0 ω); μ]).toNNReal)
      (gaussianReal 0 (Var[fun ω ↦ φ (O 0 ω); μ]).toNNReal) := HasLaw.id
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun i ω ↦ φ (O i ω)) hY h2
    hX.indep hX.ident
  have hc := hclt.tendsto_charFun s
  rw [Measure.map_id, hvar] at hc
  convert hc using 3 with m
  congr 1
  funext ω
  simp [normalizedSum, h0]

/-- The normalized sum is a measurable function of the whole sample sequence. -/
theorem measurable_normalizedSum_seq {𝒪 : Type*} [MeasurableSpace 𝒪] {φ : 𝒪 → ℝ}
    (hφ : Measurable φ) (m : ℕ) :
    Measurable fun x : ℕ → 𝒪 ↦ (√(m : ℝ))⁻¹ * ∑ j ∈ range m, φ (x j) :=
  (Finset.measurable_sum _ fun j _ ↦ hφ.comp (measurable_pi_apply j)).const_mul _

/-- The normalized sum of an i.i.d. sample is almost everywhere measurable. -/
theorem aemeasurable_normalizedSum {𝒪 : Type*} [MeasurableSpace 𝒪] {μ : Measure Ω}
    {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {φ : 𝒪 → ℝ} (hφ : Measurable φ) (m : ℕ) :
    AEMeasurable (normalizedSum φ O m) μ :=
  (Finset.aemeasurable_fun_sum _ fun j _ ↦ hφ.comp_aemeasurable (hO.aemeasurable j)).const_mul _

/-- **Independent samples, joint central limit theorem for a linear combination.** Let
`O i` (`i` in a finite index type) be i.i.d. samples that are mutually independent as sequences,
`φ i` centered square integrable influence functions, `N i n → ∞` sample sizes and `a i` real
coefficients. Then `∑ i, a i · (N i n)^{-1/2} ∑_{j < N i n} φ i (O i j)` converges in
distribution to the centered Gaussian with variance `∑ i, a i² E φ i (O i 0)²`. The proof
multiplies the characteristic functions of the independent summands (Lévy's continuity theorem
in Mathlib does the rest). -/
theorem tendstoInDistribution_sum_normalizedSum {ι : Type*} [Fintype ι] {𝒪 : ι → Type*}
    [∀ i, MeasurableSpace (𝒪 i)] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ∀ i, ℕ → Ω → 𝒪 i} (hO : ∀ i, IsIIDSample (O i) μ)
    (hind : iIndepFun (fun i ω ↦ fun j ↦ O i j ω) μ) {φ : ∀ i, 𝒪 i → ℝ}
    (hφ : ∀ i, Measurable (φ i)) (h2 : ∀ i, MemLp (fun ω ↦ φ i (O i 0 ω)) 2 μ)
    (h0 : ∀ i, μ[fun ω ↦ φ i (O i 0 ω)] = 0) {N : ι → ℕ → ℕ}
    (hN : ∀ i, Tendsto (N i) atTop atTop) (a : ι → ℝ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (∑ i, a i ^ 2 * μ[fun ω ↦ φ i (O i 0 ω) ^ 2]).toNNReal) P') :
    TendstoInDistribution (fun n ω ↦ ∑ i, a i * normalizedSum (φ i) (O i) (N i n) ω) atTop Y
      (fun _ ↦ μ) P' := by
  set v : ι → ℝ := fun i ↦ μ[fun ω ↦ φ i (O i 0 ω) ^ 2] with hv
  have hv0 : ∀ i, 0 ≤ v i := fun i ↦ integral_nonneg fun ω ↦ sq_nonneg _
  have hmeas : ∀ i n, AEMeasurable (fun ω ↦ a i * normalizedSum (φ i) (O i) (N i n) ω) μ :=
    fun i n ↦ (aemeasurable_normalizedSum (hO i) (hφ i) (N i n)).const_mul _
  refine TendstoInDistribution.of_tendsto_charFun
    (fun n ↦ Finset.aemeasurable_fun_sum _ fun i _ ↦ hmeas i n) hY.aemeasurable fun t ↦ ?_
  have hprod : ∀ n, charFun (μ.map fun ω ↦ ∑ i, a i * normalizedSum (φ i) (O i) (N i n) ω) t =
      ∏ i, charFun (μ.map (normalizedSum (φ i) (O i) (N i n))) (a i * t) := by
    intro n
    have hI : iIndepFun (fun i ω ↦ a i * normalizedSum (φ i) (O i) (N i n) ω) μ := by
      have := hind.comp (fun i (x : ℕ → 𝒪 i) ↦
          a i * ((√(N i n : ℝ))⁻¹ * ∑ j ∈ range (N i n), φ i (x j)))
        fun i ↦ (measurable_normalizedSum_seq (hφ i) (N i n)).const_mul _
      exact this
    rw [hI.charFun_map_fun_sum_eq_prod (hmeas · n), Finset.prod_apply]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    exact charFun_map_mul_comp (aemeasurable_normalizedSum (hO i) (hφ i) (N i n)) (a i) t
  simp_rw [hprod]
  have hlim : Tendsto (fun n ↦ ∏ i, charFun (μ.map (normalizedSum (φ i) (O i) (N i n))) (a i * t))
      atTop (𝓝 (∏ i, charFun (gaussianReal 0 (v i).toNNReal) (a i * t))) :=
    tendsto_finsetProd _ fun i _ ↦
      (tendsto_charFun_normalizedSum (hO i) (hφ i) (h2 i) (h0 i) (a i * t)).comp (hN i)
  convert hlim using 2
  rw [hY.map_eq, charFun_gaussianReal]
  simp_rw [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  have hsum0 : 0 ≤ ∑ i, a i ^ 2 * v i := sum_nonneg fun i _ ↦ mul_nonneg (sq_nonneg _) (hv0 i)
  rw [Real.coe_toNNReal _ hsum0]
  simp only [Real.coe_toNNReal _ (hv0 _), ofReal_zero, mul_zero, zero_mul, zero_sub, ofReal_sum,
    ofReal_mul, ofReal_pow]
  rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-! ### Sample sizes in a fixed ratio -/

/-- If `N n / n → r > 0`, then `N n → ∞`. -/
theorem tendsto_atTop_of_div_tendsto {N : ℕ → ℕ} {r : ℝ} (hr : 0 < r)
    (hN : Tendsto (fun n ↦ (N n : ℝ) / n) atTop (𝓝 r)) : Tendsto N atTop atTop := by
  have h := hN.pos_mul_atTop hr tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun n ↦ (N n : ℝ)) atTop atTop := by
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  exact tendsto_natCast_atTop_iff.1 h'

/-- If `N n / n → r > 0`, then `√(n / N n) → (√r)⁻¹`. -/
theorem tendsto_sqrt_div_of_div_tendsto {N : ℕ → ℕ} {r : ℝ} (hr : 0 < r)
    (hN : Tendsto (fun n ↦ (N n : ℝ) / n) atTop (𝓝 r)) :
    Tendsto (fun n : ℕ ↦ √((n : ℝ) / N n)) atTop (𝓝 (√r)⁻¹) := by
  have h := (hN.inv₀ hr.ne').sqrt
  rw [Real.sqrt_inv] at h
  refine h.congr fun n ↦ ?_
  rw [inv_div]

/-! ### Convergence and boundedness in probability -/

/-- Convergence in probability along a sequence of indices tending to infinity. -/
theorem _root_.MeasureTheory.TendstoInMeasure.comp_tendsto {E : Type*} [EDist E]
    {μ : Measure Ω} {f : ℕ → Ω → E} {g : Ω → E} (h : TendstoInMeasure μ f atTop g)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    TendstoInMeasure μ (fun n ↦ f (N n)) atTop g :=
  fun ε hε ↦ (h ε hε).comp hN

/-- A deterministic sequence tending to zero tends to zero in probability. -/
theorem tendstoInMeasure_const_of_tendsto {μ : Measure Ω} {a : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 0)) : TendstoInMeasure μ (fun n (_ : Ω) ↦ a n) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_order.1 (tendsto_norm_zero.comp ha)).2 ε hε] with n hn
  have : {x : Ω | ε ≤ ‖a n - (0 : Ω → ℝ) x‖} = ∅ := by
    ext x
    simp only [Pi.zero_apply, sub_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_le]
    exact hn
  rw [this, measure_empty]

/-- Finite sums of sequences tending to zero in probability tend to zero in probability. -/
theorem tendstoInMeasure_finset_sum {ι : Type*} (s : Finset ι) {μ : Measure Ω}
    {X : ι → ℕ → Ω → ℝ} (h : ∀ i ∈ s, TendstoInMeasure μ (X i) atTop 0) :
    TendstoInMeasure μ (fun n ω ↦ ∑ i ∈ s, X i n ω) atTop 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using tendstoInMeasure_const_of_tendsto (μ := μ) (a := fun _ ↦ 0) tendsto_const_nhds
  | insert j s hj ih =>
    have h1 := (h j (mem_insert_self j s)).add (ih fun i hi ↦ h i (mem_insert_of_mem hi))
    rw [add_zero] at h1
    convert h1 using 1
    funext n ω
    simp [sum_insert hj]

/-- Bounded in probability: for every `η > 0` there is `M > 0` with eventually
`μ {M ≤ |X n|} ≤ η`. -/
def BoundedInProbability (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, μ {ω | M ≤ |X n ω|} ≤ η

/-- A sequence tending to zero in probability is bounded in probability. -/
theorem boundedInProbability_of_tendstoInMeasure {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (h : TendstoInMeasure μ X atTop 0) : BoundedInProbability μ X := by
  intro η hη
  rw [tendstoInMeasure_iff_norm] at h
  refine ⟨1, one_pos, ?_⟩
  have := (ENNReal.tendsto_nhds_zero.1 (h 1 one_pos)) η hη
  filter_upwards [this] with n hn
  simpa [Real.norm_eq_abs] using hn

/-- The sum of two sequences bounded in probability is bounded in probability. -/
theorem BoundedInProbability.add {μ : Measure Ω} {X Y : ℕ → Ω → ℝ}
    (hX : BoundedInProbability μ X) (hY : BoundedInProbability μ Y) :
    BoundedInProbability μ (fun n ω ↦ X n ω + Y n ω) := by
  intro η hη
  obtain ⟨M₁, hM₁, h₁⟩ := hX (η / 2) (ENNReal.half_pos hη.ne')
  obtain ⟨M₂, hM₂, h₂⟩ := hY (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨M₁ + M₂, by linarith, ?_⟩
  filter_upwards [h₁, h₂] with n hn₁ hn₂
  calc μ {ω | M₁ + M₂ ≤ |X n ω + Y n ω|}
      ≤ μ ({ω | M₁ ≤ |X n ω|} ∪ {ω | M₂ ≤ |Y n ω|}) := by
        refine measure_mono fun ω hω ↦ ?_
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        by_contra! hlt
        have := abs_add_le (X n ω) (Y n ω)
        linarith [hlt.1, hlt.2]
    _ ≤ μ {ω | M₁ ≤ |X n ω|} + μ {ω | M₂ ≤ |Y n ω|} := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hn₁ hn₂
    _ = η := ENNReal.add_halves η

/-- A sequence bounded in probability times an eventually bounded deterministic sequence is
bounded in probability. -/
theorem BoundedInProbability.const_mul {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX : BoundedInProbability μ X) {c : ℕ → ℝ} {B : ℝ} (hc : ∀ᶠ n in atTop, |c n| ≤ B) :
    BoundedInProbability μ (fun n ω ↦ c n * X n ω) := by
  intro η hη
  obtain ⟨M, hM, h⟩ := hX η hη
  refine ⟨(|B| + 1) * M, by positivity, ?_⟩
  filter_upwards [h, hc] with n hn hcn
  refine (measure_mono fun ω hω ↦ ?_).trans hn
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra! hlt
  rw [abs_mul] at hω
  have hB : |c n| ≤ |B| + 1 := by linarith [le_abs_self B]
  have : |c n| * |X n ω| ≤ (|B| + 1) * |X n ω| :=
    mul_le_mul_of_nonneg_right hB (abs_nonneg _)
  have : (|B| + 1) * |X n ω| < (|B| + 1) * M :=
    mul_lt_mul_of_pos_left hlt (by positivity)
  linarith

/-- **The normalized sum is bounded in probability, uniformly in the sample size** (Chebyshev). -/
theorem normalizedSum_bounded {𝒪 : Type*} [MeasurableSpace 𝒪] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ) {φ : 𝒪 → ℝ}
    (hφ : Measurable φ) (h2 : MemLp (fun ω ↦ φ (O 0 ω)) 2 μ) (h0 : μ[fun ω ↦ φ (O 0 ω)] = 0)
    (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ m, μ {ω | M ≤ |normalizedSum φ O m ω|} ≤ η := by
  set E := μ[fun ω ↦ φ (O 0 ω) ^ 2] with hE
  have hE0 : 0 ≤ E := integral_nonneg fun ω ↦ sq_nonneg _
  rcases eq_or_ne η ⊤ with hηt | hηt
  · exact ⟨1, one_pos, fun m ↦ hηt ▸ le_top⟩
  set e : ℝ := min η.toReal 1 with he
  have he0 : 0 < e := lt_min (ENNReal.toReal_pos hη.ne' hηt) one_pos
  have hel : ENNReal.ofReal e ≤ η := by
    rw [← ENNReal.ofReal_toReal hηt]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  set M : ℝ := √(E / e) + 1 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M, hM0, fun m ↦ ?_⟩
  refine (measure_le_abs_inv_sqrt_mul_sum_le hO hφ h2 h0 m hM0).trans
    ((ENNReal.ofReal_le_ofReal ?_).trans hel)
  rw [div_le_iff₀ (by positivity)]
  have hs : E / e ≤ M ^ 2 := by
    have h1 : √(E / e) ^ 2 = E / e := Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (E / e)]
  calc E = E / e * e := by field_simp
    _ ≤ M ^ 2 * e := mul_le_mul_of_nonneg_right hs he0.le
    _ = e * M ^ 2 := by ring

/-! ### The delta step along arbitrary sequences -/

/-- **Linearization in probability.** Let `T i n → θ i` in probability for every coordinate of a
finite index type, with `√n (T i n - θ i)` bounded in probability, and let `g` have Fréchet
derivative `L` at `θ`. Then
`√n (g (T n) - g θ) - ∑ i, L (eᵢ) √n (T i n - θ i) → 0` in probability. No sampling structure
is used: this is the deterministic part of the delta method. -/
theorem tendstoInMeasure_sqrt_mul_comp_sub_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} {T : ι → ℕ → Ω → ℝ} {θ : ι → ℝ}
    (hT : ∀ i, TendstoInMeasure μ (T i) atTop (fun _ ↦ θ i))
    (hB : ∀ i, BoundedInProbability μ (fun (n : ℕ) ω ↦ √(n : ℝ) * (T i n ω - θ i)))
    {g : (ι → ℝ) → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt g L θ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ √(n : ℝ) * (g (fun i ↦ T i n ω) - g θ) -
      ∑ i, L (Pi.single i 1) * (√(n : ℝ) * (T i n ω - θ i))) atTop 0 := by
  set c : ι → ℝ := fun i ↦ L (Pi.single i 1) with hc
  set ρ : (ι → ℝ) → ℝ := fun x ↦ (g x - g θ - L (x - θ)) / ‖x - θ‖ with hρ
  have hkey : ∀ x, g x - g θ - L (x - θ) = ρ x * ‖x - θ‖ := by
    intro x
    by_cases hx : x = θ
    · subst hx
      simp
    · have hn : ‖x - θ‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hx)
      simp only [hρ]
      field_simp
  have hρθ : ρ θ = 0 := by simp [hρ]
  have hρc : ContinuousAt ρ θ := by
    rw [ContinuousAt, hρθ, tendsto_zero_iff_norm_tendsto_zero]
    refine (hasFDerivAt_iff_tendsto.1 hg).congr fun x ↦ ?_
    simp only [hρ, norm_div, norm_norm]
    ring
  clear_value ρ
  have hcons : TendstoInMeasure μ (fun n ω ↦ ρ (fun i ↦ T i n ω)) atTop 0 := by
    have := tendstoInMeasure_pi_comp hT hρc
    rw [hρθ] at this
    exact this
  have hbdd := boundedInProbability_norm_pi (μ := μ)
    (Y := fun i (n : ℕ) ω ↦ √(n : ℝ) * (T i n ω - θ i)) hB
  refine (tendstoInMeasure_mul_of_bounded hcons hbdd).congr'
    (Eventually.of_forall fun n ↦ Eventually.of_forall fun ω ↦ ?_) EventuallyEq.rfl
  have hL : L ((fun i ↦ T i n ω) - θ) = ∑ i, c i * (T i n ω - θ i) := by
    rw [clm_apply_eq_sum_single L]
    rfl
  have hnorm : ‖fun i ↦ √(n : ℝ) * (T i n ω - θ i)‖ = √(n : ℝ) * ‖(fun i ↦ T i n ω) - θ‖ := by
    have : (fun i ↦ √(n : ℝ) * (T i n ω - θ i)) = √(n : ℝ) • ((fun i ↦ T i n ω) - θ) := by
      funext i
      simp [smul_eq_mul]
    rw [this, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hk := hkey (fun i ↦ T i n ω)
  rw [hL] at hk
  have hsum : ∑ i, L (Pi.single i 1) * (√(n : ℝ) * (T i n ω - θ i)) =
      √(n : ℝ) * ∑ i, c i * (T i n ω - θ i) := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hnorm]
  beta_reduce
  rw [hsum]
  linear_combination (-√(n : ℝ)) * hk

/-! ### One estimator along a sample size sequence -/

/-- **Slutsky step for one study.** If `θhat` is asymptotically linear at `θ` with influence
function `φ` for an i.i.d. sample `O`, and the sample size `N n` satisfies `N n / n → r > 0`,
then `√n (θhat (N n) - θ) - r^{-1/2} (N n)^{-1/2} ∑_{j < N n} φ (O j) → 0` in probability. -/
theorem IsAsymptoticallyLinear.sqrt_mul_sub_sub_normalizedSum {𝒪 : Type*} [MeasurableSpace 𝒪]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ)
    {θhat : ℕ → Ω → ℝ} {θ : ℝ} {φ : 𝒪 → ℝ} (h : IsAsymptoticallyLinear θhat θ φ O μ)
    {N : ℕ → ℕ} {r : ℝ} (hr : 0 < r) (hN : Tendsto (fun n ↦ (N n : ℝ) / n) atTop (𝓝 r)) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ √(n : ℝ) * (θhat (N n) ω - θ) -
      (√r)⁻¹ * normalizedSum φ O (N n) ω) atTop 0 := by
  have hNt := tendsto_atTop_of_div_tendsto hr hN
  have hs := tendsto_sqrt_div_of_div_tendsto hr hN
  set s : ℕ → ℝ := fun n ↦ √((n : ℝ) / N n) with hsdef
  have hR := h.remainder.comp_tendsto hNt
  have hsB : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n in atTop, μ {ω : Ω | M ≤ |s n|} ≤ η := by
    intro η _
    refine ⟨(√r)⁻¹ + 1, by positivity, ?_⟩
    have hev := (tendsto_order.1 hs).2 ((√r)⁻¹ + 1) (by linarith)
    filter_upwards [hev] with n hn
    have hsn : 0 ≤ s n := Real.sqrt_nonneg _
    have : {ω : Ω | (√r)⁻¹ + 1 ≤ |s n|} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le,
        abs_of_nonneg hsn]
      exact hn
    rw [this, measure_empty]
    exact bot_le
  have hA := tendstoInMeasure_mul_of_bounded hR hsB
  have hD : TendstoInMeasure μ (fun n (_ : Ω) ↦ s n - (√r)⁻¹) atTop 0 :=
    tendstoInMeasure_const_of_tendsto (by simpa using hs.sub_const (√r)⁻¹)
  have hSB : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ n in atTop, μ {ω | M ≤ |normalizedSum φ O (N n) ω|} ≤ η := by
    intro η hη
    obtain ⟨M, hM, hb⟩ := normalizedSum_bounded hO h.measurable h.memLp h.integral_eq_zero η hη
    exact ⟨M, hM, Eventually.of_forall fun n ↦ hb (N n)⟩
  have hB := tendstoInMeasure_mul_of_bounded hD hSB
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [hNt.eventually (eventually_ge_atTop 1)] with n hn
  refine Eventually.of_forall fun ω ↦ ?_
  have hN0 : (0 : ℝ) < N n := by exact_mod_cast hn
  have hsq : s n * √(N n : ℝ) = √(n : ℝ) := by
    rw [hsdef, ← Real.sqrt_mul (div_nonneg n.cast_nonneg hN0.le), div_mul_cancel₀ _ hN0.ne']
  simp only [Pi.add_apply, normalizedSum]
  rw [← hsq]
  ring

/-- Along a sample size sequence in a fixed ratio, `√n (θhat (N n) - θ)` is bounded in
probability. -/
theorem IsAsymptoticallyLinear.boundedInProbability_of_sizes {𝒪 : Type*} [MeasurableSpace 𝒪]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪} (hO : IsIIDSample O μ)
    {θhat : ℕ → Ω → ℝ} {θ : ℝ} {φ : 𝒪 → ℝ} (h : IsAsymptoticallyLinear θhat θ φ O μ)
    {N : ℕ → ℕ} {r : ℝ} (hr : 0 < r) (hN : Tendsto (fun n ↦ (N n : ℝ) / n) atTop (𝓝 r)) :
    BoundedInProbability μ (fun (n : ℕ) ω ↦ √(n : ℝ) * (θhat (N n) ω - θ)) := by
  have h1 := boundedInProbability_of_tendstoInMeasure (h.sqrt_mul_sub_sub_normalizedSum hO hr hN)
  have h2 : BoundedInProbability μ (fun n ω ↦ (√r)⁻¹ * normalizedSum φ O (N n) ω) := by
    have hS : BoundedInProbability μ (fun n ω ↦ normalizedSum φ O (N n) ω) := by
      intro η hη
      obtain ⟨M, hM, hb⟩ :=
        normalizedSum_bounded hO h.measurable h.memLp h.integral_eq_zero η hη
      exact ⟨M, hM, Eventually.of_forall fun n ↦ hb (N n)⟩
    exact hS.const_mul (c := fun _ ↦ (√r)⁻¹) (B := (√r)⁻¹)
      (Eventually.of_forall fun _ ↦ le_of_eq (abs_of_nonneg (by positivity)))
  have := h1.add h2
  convert this using 3 with n ω
  ring

/-! ### The delta method for independent samples of different sizes -/

section SeveralSamples

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒪 : ι → Type*} [∀ i, MeasurableSpace (𝒪 i)]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ∀ i, ℕ → Ω → 𝒪 i}
  {θhat : ι → ℕ → Ω → ℝ} {θ : ι → ℝ} {φ : ∀ i, 𝒪 i → ℝ} {N : ι → ℕ → ℕ} {r : ι → ℝ}

/-- **Linearization for independent samples of different sizes.** With `θhat i` asymptotically
linear in its own i.i.d. sample `O i`, sample sizes `N i n` with `N i n / n → r i > 0`, and `g`
differentiable at `θ` with derivative `L`,
`√n (g (θhat · (N · n)) - g θ) - ∑ i, L (eᵢ) r i^{-1/2} (N i n)^{-1/2} ∑_{j < N i n} φ i (O i j)`
tends to zero in probability. Independence between the samples is not needed for this step. -/
theorem tendstoInMeasure_sqrt_mul_comp_sub_normalizedSum_of_sizes
    (hO : ∀ i, IsIIDSample (O i) μ)
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) (O i) μ)
    (hr : ∀ i, 0 < r i) (hN : ∀ i, Tendsto (fun n ↦ (N i n : ℝ) / n) atTop (𝓝 (r i)))
    {g : (ι → ℝ) → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt g L θ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ √(n : ℝ) * (g (fun i ↦ θhat i (N i n) ω) - g θ) -
      ∑ i, L (Pi.single i 1) * (√(r i))⁻¹ * normalizedSum (φ i) (O i) (N i n) ω) atTop 0 := by
  have hT : ∀ i, TendstoInMeasure μ (fun n ↦ θhat i (N i n)) atTop (fun _ ↦ θ i) := fun i ↦
    ((h i).isConsistent (hO i)).comp_tendsto (tendsto_atTop_of_div_tendsto (hr i) (hN i))
  have hlin := tendstoInMeasure_sqrt_mul_comp_sub_sum hT
    (fun i ↦ (h i).boundedInProbability_of_sizes (hO i) (hr i) (hN i)) hg
  have hsl := tendstoInMeasure_finset_sum univ (μ := μ)
    (X := fun i (n : ℕ) ω ↦ L (Pi.single i 1) * (√(n : ℝ) * (θhat i (N i n) ω - θ i) -
      (√(r i))⁻¹ * normalizedSum (φ i) (O i) (N i n) ω))
    fun i _ ↦ by
      have := ((h i).sqrt_mul_sub_sub_normalizedSum (hO i) (hr i) (hN i)).const_mul
        (L (Pi.single i 1))
      convert this using 1
      funext x
      simp
  have hsum := hlin.add hsl
  rw [add_zero] at hsum
  convert hsum using 1
  funext n ω
  simp only [Pi.add_apply, mul_sub, sum_sub_distrib]
  have : ∀ i, L (Pi.single i 1) * ((√(r i))⁻¹ * normalizedSum (φ i) (O i) (N i n) ω) =
      L (Pi.single i 1) * (√(r i))⁻¹ * normalizedSum (φ i) (O i) (N i n) ω := fun i ↦ by ring
  simp only [this]
  ring

/-- **The delta method for independent samples of different sizes.** Let `O i` (`i` in a finite
index type) be i.i.d. samples on one probability space, mutually independent as sequences; let
`θhat i` be asymptotically linear at `θ i` with influence function `φ i` in its own sample (at its
own sample size); let the size of sample `i` be `N i n` with `N i n / n → r i > 0`; let `g` have
Fréchet derivative `L` at `θ`, and let each `g (θhat · (N · n))` be almost everywhere measurable.
Then `√n (g (θhat · (N · n)) - g θ)` converges in distribution to the centered Gaussian with
variance `∑ i, cᵢ² E φ i (O i 0)² / r i`, `cᵢ = L (eᵢ)`.

The estimators are not required to be functions of their own samples: only their linear parts
`∑_{j < N i n} φ i (O i j)` are, and the remainders are handled in probability. -/
theorem tendstoInDistribution_comp_hasFDerivAt_of_sizes
    (hO : ∀ i, IsIIDSample (O i) μ) (hind : iIndepFun (fun i ω ↦ fun j ↦ O i j ω) μ)
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) (O i) μ)
    (hr : ∀ i, 0 < r i) (hN : ∀ i, Tendsto (fun n ↦ (N i n : ℝ) / n) atTop (𝓝 (r i)))
    {g : (ι → ℝ) → ℝ} {L : (ι → ℝ) →L[ℝ] ℝ} (hg : HasFDerivAt g L θ)
    (hmeas : ∀ n, AEMeasurable (fun ω ↦ g (fun i ↦ θhat i (N i n) ω)) μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0
      (∑ i, L (Pi.single i 1) ^ 2 * μ[fun ω ↦ φ i (O i 0 ω) ^ 2] / r i).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (g (fun i ↦ θhat i (N i n) ω) - g θ))
      atTop Y (fun _ ↦ μ) P' := by
  have hvar : ∑ i, L (Pi.single i 1) ^ 2 * μ[fun ω ↦ φ i (O i 0 ω) ^ 2] / r i =
      ∑ i, (L (Pi.single i 1) * (√(r i))⁻¹) ^ 2 * μ[fun ω ↦ φ i (O i 0 ω) ^ 2] := by
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_pow, inv_pow, Real.sq_sqrt (hr i).le]
    ring
  rw [hvar] at hY
  have hclt := tendstoInDistribution_sum_normalizedSum hO hind (fun i ↦ (h i).measurable)
    (fun i ↦ (h i).memLp) (fun i ↦ (h i).integral_eq_zero)
    (fun i ↦ tendsto_atTop_of_div_tendsto (hr i) (hN i))
    (fun i ↦ L (Pi.single i 1) * (√(r i))⁻¹) hY
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Y hclt ?_
    fun n ↦ ((hmeas n).sub_const _).const_mul _
  have := tendstoInMeasure_sqrt_mul_comp_sub_normalizedSum_of_sizes hO h hr hN hg
  convert this using 1

end SeveralSamples

end CausalInference
