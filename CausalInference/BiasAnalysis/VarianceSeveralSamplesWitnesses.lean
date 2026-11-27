/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.VarianceSeveralSamples
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Concrete sampling schemes for the asymptotic variance theorems

For each asymptotic theorem of `BiasAnalysis.VarianceCovariance` and
`BiasAnalysis.VarianceSeveralSamples`, an explicit sampling scheme is given that meets every
hypothesis, so that the conclusion holds for a real sampling scheme. The probability space is a
grid of independent coins `ω a b` (`gridMeasure`, a product of Bernoulli laws built with
`Measure.infinitePi`). Its rows are mutually independent i.i.d. samples
(`gridMeasure_rows_isIIDSample`, `gridMeasure_iIndepFun_rows`), which gives independent studies;
read the other way, its rows are one i.i.d. sample of vectors of independent coins
(`gridMeasure_isIIDSample`, `gridMeasure_indepFun_coord`). The estimators are sample proportions,
their influence functions the centered indicators, and their binomial variances `p (1 - p)` are
proved.

* One sample: `greenland_nondifferential_asymptotic_instance`,
  `greenland_differential_asymptotic_instance`, `marshall_asymptotic_instance`,
  `ivPooled_asymptotic_instance`.
* Several studies of different sizes: `greenland_nondifferential_of_sizes_instance`,
  `greenland_differential_of_sizes_instance`, `marshall_of_sizes_instance`,
  `ivPooled_of_sizes_instance`, and `ivPooled_estimated_of_sizes_instance`, the last with the
  printed weights (inverse binomial variance estimates `p̂ᵢ (1 - p̂ᵢ) / Nᵢ`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset unitInterval
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace BiasAnalysis.SamplingWitnesses

open VarianceFormulas VarianceCovariance VarianceSeveralSamples

/-! ### Coin flips on a grid -/

/-- The indicator of `true`. -/
noncomputable def coin (b : Bool) : ℝ := if b then 1 else 0

theorem measurable_coin : Measurable coin := measurable_of_finite _

theorem coin_mem (b : Bool) : coin b = 0 ∨ coin b = 1 := by
  cases b <;> simp [coin]

/-- A coin with success probability `p`: the Bernoulli law on `Bool` with mass `p` at `true`. -/
noncomputable abbrev coinLaw (p : I) : Measure Bool := bernoulliMeasure true false p

theorem integral_coin (p : I) : ∫ b, coin b ∂(coinLaw p) = p := by
  rw [integral_bernoulliMeasure]
  simp [coin]

/-- Independent coins `ω a b` indexed by a grid `α × β`, the coin at `(a, b)` with success
probability `p a b`. -/
noncomputable def gridMeasure {α β : Type*} (p : α → β → I) : Measure (α → β → Bool) :=
  Measure.infinitePi fun a ↦ Measure.infinitePi fun b ↦ coinLaw (p a b)

instance {α β : Type*} (p : α → β → I) : IsProbabilityMeasure (gridMeasure p) := by
  unfold gridMeasure
  infer_instance

/-- All coins of the grid are mutually independent. -/
theorem gridMeasure_iIndepFun {α β : Type*} (p : α → β → I) :
    iIndepFun (fun (ab : α × β) (ω : α → β → Bool) ↦ ω ab.1 ab.2) (gridMeasure p) :=
  iIndepFun_uncurry_infinitePi' (X := fun _ _ ↦ id) (fun a b ↦ coinLaw (p a b))
    fun _ _ ↦ measurable_id

/-- The rows `ω a` of the grid are mutually independent. -/
theorem gridMeasure_iIndepFun_rows {α β : Type*} (p : α → β → I) :
    iIndepFun (fun (a : α) (ω : α → β → Bool) ↦ ω a) (gridMeasure p) :=
  iIndepFun_infinitePi (X := fun _ ↦ id) fun _ ↦ measurable_id

/-- The law of one row. -/
theorem gridMeasure_map_row {α β : Type*} (p : α → β → I) (a : α) :
    (gridMeasure p).map (fun ω ↦ ω a) = Measure.infinitePi fun b ↦ coinLaw (p a b) :=
  Measure.infinitePi_map_eval _ a

/-- The law of one coin. -/
theorem gridMeasure_map_coin {α β : Type*} (p : α → β → I) (a : α) (b : β) :
    (gridMeasure p).map (fun ω ↦ ω a b) = coinLaw (p a b) := by
  have : (fun ω : α → β → Bool ↦ ω a b) = (fun x : β → Bool ↦ x b) ∘ (fun ω ↦ ω a) := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply b) (measurable_pi_apply a),
    gridMeasure_map_row, Measure.infinitePi_map_eval]

/-- The expectation of the indicator of one coin. -/
theorem gridMeasure_integral_coin {α β : Type*} (p : α → β → I) (a : α) (b : β) :
    ∫ ω, coin (ω a b) ∂(gridMeasure p) = p a b := by
  have hm : AEMeasurable (fun ω : α → β → Bool ↦ ω a b) (gridMeasure p) :=
    ((measurable_pi_apply b).comp (measurable_pi_apply a)).aemeasurable
  rw [← integral_map hm measurable_coin.aestronglyMeasurable, gridMeasure_map_coin,
    integral_coin]

/-- **Several independent samples.** With success probability `q a` in row `a`, the rows
`fun j ↦ ω a j` are mutually independent i.i.d. samples of coins. -/
theorem gridMeasure_rows_isIIDSample {α : Type*} (q : α → I) (a : α) :
    IsIIDSample (fun (j : ℕ) (ω : α → ℕ → Bool) ↦ ω a j) (gridMeasure fun a (_ : ℕ) ↦ q a) where
  indep := (gridMeasure_iIndepFun _).precomp (g := fun j : ℕ ↦ (a, j))
    fun _ _ h ↦ (Prod.mk.inj h).2
  ident j := by
    refine ⟨((measurable_pi_apply j).comp (measurable_pi_apply a)).aemeasurable,
      ((measurable_pi_apply 0).comp (measurable_pi_apply a)).aemeasurable, ?_⟩
    rw [gridMeasure_map_coin, gridMeasure_map_coin]

/-- **One sample of vectors.** With success probability `q b` in column `b`, the rows `ω j` are an
i.i.d. sample of vectors of independent coins. -/
theorem gridMeasure_isIIDSample {β : Type*} (q : β → I) :
    IsIIDSample (fun (j : ℕ) (ω : ℕ → β → Bool) ↦ ω j) (gridMeasure fun (_ : ℕ) b ↦ q b) where
  indep := gridMeasure_iIndepFun_rows _
  ident j := by
    refine ⟨(measurable_pi_apply j).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
    rw [gridMeasure_map_row, gridMeasure_map_row]

/-- In one sample of vectors, measurable functions of different coordinates of the first
observation are independent. -/
theorem gridMeasure_indepFun_coord {β : Type*} (q : β → I) {g : β → Bool → ℝ}
    (hg : ∀ b, Measurable (g b)) :
    Pairwise fun b b' ↦ IndepFun (fun ω : ℕ → β → Bool ↦ g b (ω 0 b))
      (fun ω ↦ g b' (ω 0 b')) (gridMeasure fun (_ : ℕ) b ↦ q b) := by
  intro b b' hbb
  have h := (gridMeasure_iIndepFun fun (_ : ℕ) b ↦ q b).indepFun
    (i := (0, b)) (j := (0, b')) (by simpa using hbb)
  exact h.comp (hg b) (hg b')

/-- In one sample of coin vectors, the proportion of successes in column `b` is asymptotically
linear at `q b` with the binomial variance `q b (1 - q b)`. -/
theorem gridMeasure_sampleProportion {β : Type*} (q : β → I) (b : β) :
    IsAsymptoticallyLinear (sampleMean (fun x ↦ coin (x b)) fun j (ω : ℕ → β → Bool) ↦ ω j)
        (q b) (fun x ↦ coin (x b) - q b) (fun j ω ↦ ω j) (gridMeasure fun (_ : ℕ) b ↦ q b) ∧
      ∫ ω, (coin (ω 0 b) - q b) ^ 2 ∂(gridMeasure fun (_ : ℕ) b ↦ q b) = q b * (1 - q b) :=
  sampleProportion_isAsymptoticallyLinear (gridMeasure_isIIDSample q)
    (measurable_coin.comp (measurable_pi_apply b)) (fun x ↦ coin_mem (x b))
    (gridMeasure_integral_coin _ 0 b)

/-- A sample size `c n` grows in the ratio `c` to `n`. -/
theorem tendsto_natCast_mul_div (c : ℕ) :
    Tendsto (fun n : ℕ ↦ ((c * n : ℕ) : ℝ) / n) atTop (𝓝 (c : ℝ)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- A point of the unit interval given by a real number in `[0, 1]`. -/
abbrev pt (x : ℝ) (h₀ : 0 ≤ x := by norm_num) (h₁ : x ≤ 1 := by norm_num) : I := ⟨x, h₀, h₁⟩

/-! ### The one-sample theorems of `VarianceCovariance` -/

/-- Success probabilities `(SE, SP, pe₁, pe₀) = (0.9, 0.9, 0.5, 0.3)` of the one-sample Greenland
instance. -/
noncomputable def greenlandQ : Fin 4 → I := ![pt 0.9, pt 0.9, pt 0.5, pt 0.3]

theorem greenlandQ_coe (i : Fin 4) : (greenlandQ i : ℝ) = ![0.9, 0.9, 0.5, 0.3] i := by
  fin_cases i <;> rfl

/-- **`greenland_nondifferential_asymptotic` holds for a real sampling scheme.** Each observation
is a vector of four independent coins: the classification of a truly exposed validation subject
(success probability `SE = 0.9`), of a truly unexposed one (`SP = 0.9`), the observed exposure of a
case (`pe₁ = 0.5`) and of a control (`pe₀ = 0.3`). The four estimators are the sample proportions,
their influence functions the centered indicators, and the input variances are the binomial
variances `p (1 - p)`, proved here, with `D₁ = D₀ = 1` (one case and one control per
observation). Every hypothesis of `greenland_nondifferential_asymptotic` holds, so the plug-in
adjusted log odds ratio is asymptotically linear with asymptotic variance
`greenlandNondiff 0.09 0.09 0.9 0.9 0.5 1 0.3 1`. -/
theorem greenland_nondifferential_asymptotic_instance :
    let μ := gridMeasure fun (_ : ℕ) b ↦ greenlandQ b
    let O : ℕ → (ℕ → Fin 4 → Bool) → Fin 4 → Bool := fun j ω ↦ ω j
    let θhat : Fin 4 → ℕ → (ℕ → Fin 4 → Bool) → ℝ := fun i ↦ sampleMean (fun x ↦ coin (x i)) O
    let φ : Fin 4 → (Fin 4 → Bool) → ℝ := fun i x ↦ coin (x i) - ![0.9, 0.9, 0.5, 0.3] i
    IsIIDSample O μ ∧
      (∀ i, IsAsymptoticallyLinear (θhat i) (![0.9, 0.9, 0.5, 0.3] i) (φ i) O μ) ∧
      (Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ) ∧
      (∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] =
        ![0.9 * (1 - 0.9), 0.9 * (1 - 0.9), 0.5 * (1 - 0.5) / 1, 0.3 * (1 - 0.3) / 1] i) ∧
      (0 : ℝ) < 0.5 + 0.9 - 1 ∧ (0 : ℝ) < 0.9 - 0.5 ∧ (0 : ℝ) < 1 ∧
      (0 : ℝ) < 0.3 + 0.9 - 1 ∧ (0 : ℝ) < 0.9 - 0.3 ∧ (0 : ℝ) < 1 ∧
      IsAsymptoticallyLinear
          (fun n ω ↦ logORSeSp (θhat 0 n ω) (θhat 1 n ω) (θhat 2 n ω) (θhat 0 n ω)
            (θhat 1 n ω) (θhat 3 n ω))
          (logORSeSp 0.9 0.9 0.5 0.9 0.9 0.3)
          (fun x ↦ ∑ i, greenlandNondiffGrad 0.9 0.9 0.5 0.3 i * φ i x) O μ ∧
        μ[fun ω ↦ (∑ i, greenlandNondiffGrad 0.9 0.9 0.5 0.3 i * φ i (O 0 ω)) ^ 2] =
          greenlandNondiff (0.9 * (1 - 0.9)) (0.9 * (1 - 0.9)) 0.9 0.9 0.5 1 0.3 1 := by
  intro μ O θhat φ
  have hO : IsIIDSample O μ := gridMeasure_isIIDSample greenlandQ
  have hAL : ∀ i, IsAsymptoticallyLinear (θhat i) (![0.9, 0.9, 0.5, 0.3] i) (φ i) O μ ∧
      μ[fun ω ↦ φ i (O 0 ω) ^ 2] =
        ![0.9, 0.9, 0.5, 0.3] i * (1 - ![(0.9 : ℝ), 0.9, 0.5, 0.3] i) := by
    intro i
    have := gridMeasure_sampleProportion greenlandQ i
    rw [greenlandQ_coe] at this
    exact this
  have hind : Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ :=
    gridMeasure_indepFun_coord greenlandQ (g := fun b x ↦ coin x - ![0.9, 0.9, 0.5, 0.3] b)
      fun _ ↦ measurable_coin.sub_const _
  have hσ : ∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] =
      ![0.9 * (1 - 0.9), 0.9 * (1 - 0.9), 0.5 * (1 - 0.5) / 1, 0.3 * (1 - 0.3) / 1] i := by
    intro i
    rw [(hAL i).2]
    fin_cases i <;> norm_num
  have hpos : (0 : ℝ) < 0.5 + 0.9 - 1 ∧ (0 : ℝ) < 0.9 - 0.5 ∧ (0 : ℝ) < 1 ∧
      (0 : ℝ) < 0.3 + 0.9 - 1 ∧ (0 : ℝ) < 0.9 - 0.3 ∧ (0 : ℝ) < 1 := by norm_num
  obtain ⟨hA₁, hB₁, hD₁, hA₀, hB₀, hD₀⟩ := hpos
  exact ⟨hO, fun i ↦ (hAL i).1, hind, hσ, hA₁, hB₁, hD₁, hA₀, hB₀, hD₀,
    greenland_nondifferential_asymptotic hO (fun i ↦ (hAL i).1) hind hσ hA₁ hB₁ hD₁ hA₀ hB₀ hD₀⟩

/-- The hypotheses shared by the one-sample instances: for a vector of independent coins with
success probabilities `q`, the sample proportions are asymptotically linear with the centered
indicators as influence functions, these are pairwise independent, and their second moments are
the binomial variances. -/
theorem oneSample_hypotheses {k : ℕ} (q : Fin k → I) (v : Fin k → ℝ)
    (hv : ∀ i, (q i : ℝ) = v i) :
    IsIIDSample (fun j (ω : ℕ → Fin k → Bool) ↦ ω j) (gridMeasure fun (_ : ℕ) b ↦ q b) ∧
      (∀ i, IsAsymptoticallyLinear (sampleMean (fun x ↦ coin (x i)) fun j ω ↦ ω j) (v i)
        (fun x ↦ coin (x i) - v i) (fun j ω ↦ ω j) (gridMeasure fun (_ : ℕ) b ↦ q b)) ∧
      (Pairwise fun i j ↦ IndepFun (fun ω : ℕ → Fin k → Bool ↦ coin (ω 0 i) - v i)
        (fun ω ↦ coin (ω 0 j) - v j) (gridMeasure fun (_ : ℕ) b ↦ q b)) ∧
      ∀ i, ∫ ω, (coin (ω 0 i) - v i) ^ 2 ∂(gridMeasure fun (_ : ℕ) b ↦ q b) =
        v i * (1 - v i) := by
  have hAL : ∀ i, _ := fun i ↦ gridMeasure_sampleProportion q i
  simp only [hv] at hAL
  exact ⟨gridMeasure_isIIDSample q, fun i ↦ (hAL i).1,
    gridMeasure_indepFun_coord q (g := fun b x ↦ coin x - v b)
      (fun _ ↦ measurable_coin.sub_const _),
    fun i ↦ (hAL i).2⟩

/-- Success probabilities `(SE₁, SP₁, pe₁, SE₀, SP₀, pe₀) = (0.9, 0.9, 0.5, 0.8, 0.9, 0.3)` of the
one-sample differential Greenland instance. -/
noncomputable def greenlandDiffQ : Fin 6 → I :=
  ![pt 0.9, pt 0.9, pt 0.5, pt 0.8, pt 0.9, pt 0.3]

/-- **`greenland_differential_asymptotic` holds for a real sampling scheme**: six independent
coins per observation (sensitivity and specificity among cases `0.9`, `0.9`, exposure of a case
`0.5`, sensitivity and specificity among controls `0.8`, `0.9`, exposure of a control `0.3`),
sample proportions as estimators, binomial input variances, `D₁ = D₀ = 1`. -/
theorem greenland_differential_asymptotic_instance :
    let μ := gridMeasure fun (_ : ℕ) b ↦ greenlandDiffQ b
    let v : Fin 6 → ℝ := ![0.9, 0.9, 0.5, 0.8, 0.9, 0.3]
    let O : ℕ → (ℕ → Fin 6 → Bool) → Fin 6 → Bool := fun j ω ↦ ω j
    let θhat : Fin 6 → ℕ → (ℕ → Fin 6 → Bool) → ℝ := fun i ↦ sampleMean (fun x ↦ coin (x i)) O
    let φ : Fin 6 → (Fin 6 → Bool) → ℝ := fun i x ↦ coin (x i) - v i
    IsIIDSample O μ ∧ (∀ i, IsAsymptoticallyLinear (θhat i) (v i) (φ i) O μ) ∧
      (Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ) ∧
      (∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] = ![0.9 * (1 - 0.9), 0.9 * (1 - 0.9),
        0.5 * (1 - 0.5) / 1, 0.8 * (1 - 0.8), 0.9 * (1 - 0.9), 0.3 * (1 - 0.3) / 1] i) ∧
      IsAsymptoticallyLinear
          (fun n ω ↦ logORSeSp (θhat 0 n ω) (θhat 1 n ω) (θhat 2 n ω) (θhat 3 n ω)
            (θhat 4 n ω) (θhat 5 n ω))
          (logORSeSp 0.9 0.9 0.5 0.8 0.9 0.3)
          (fun x ↦ ∑ i, greenlandGrad 0.9 0.9 0.5 0.8 0.9 0.3 i * φ i x) O μ ∧
        μ[fun ω ↦ (∑ i, greenlandGrad 0.9 0.9 0.5 0.8 0.9 0.3 i * φ i (O 0 ω)) ^ 2] =
          greenlandTerm (0.9 * (1 - 0.9)) (0.9 * (1 - 0.9)) 0.9 0.9 0.5 1 +
            greenlandTerm (0.8 * (1 - 0.8)) (0.9 * (1 - 0.9)) 0.8 0.9 0.3 1 := by
  intro μ v O θhat φ
  obtain ⟨hO, hAL, hind, hσ'⟩ := oneSample_hypotheses greenlandDiffQ v
    fun i ↦ by fin_cases i <;> rfl
  have hσ : ∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] = ![0.9 * (1 - 0.9), 0.9 * (1 - 0.9),
      0.5 * (1 - 0.5) / 1, 0.8 * (1 - 0.8), 0.9 * (1 - 0.9), 0.3 * (1 - 0.3) / 1] i := by
    intro i
    rw [hσ' i]
    fin_cases i <;> norm_num [v]
  have hv : (![0.9, 0.9, 0.5, 0.8, 0.9, 0.3] : Fin 6 → ℝ) = v := rfl
  exact ⟨hO, hAL, hind, hσ, greenland_differential_asymptotic hO (θhat := θhat)
    (by rw [hv]; exact hAL) hind hσ (by norm_num) (by norm_num) one_pos (by norm_num)
    (by norm_num) one_pos⟩

/-- Success probabilities `(PPV₁, NPV₁, pe₁, PPV₀, NPV₀, pe₀) = (0.9, 0.9, 0.5, 0.9, 0.9, 0.3)`
of the one-sample Marshall instance; the corrected proportions are `0.5` and `0.34`. -/
noncomputable def marshallQ : Fin 6 → I :=
  ![pt 0.9, pt 0.9, pt 0.5, pt 0.9, pt 0.9, pt 0.3]

/-- **`marshall_asymptotic` holds for a real sampling scheme**: six independent coins per
observation with success probabilities `marshallQ`, sample proportions as estimators, and their
binomial variances as input variances. Both corrected proportions (`0.5` and `0.34`) lie in
`(0, 1)`. -/
theorem marshall_asymptotic_instance :
    let μ := gridMeasure fun (_ : ℕ) b ↦ marshallQ b
    let v : Fin 6 → ℝ := ![0.9, 0.9, 0.5, 0.9, 0.9, 0.3]
    let O : ℕ → (ℕ → Fin 6 → Bool) → Fin 6 → Bool := fun j ω ↦ ω j
    let θhat : Fin 6 → ℕ → (ℕ → Fin 6 → Bool) → ℝ := fun i ↦ sampleMean (fun x ↦ coin (x i)) O
    let φ : Fin 6 → (Fin 6 → Bool) → ℝ := fun i x ↦ coin (x i) - v i
    IsIIDSample O μ ∧ (∀ i, IsAsymptoticallyLinear (θhat i) (v i) (φ i) O μ) ∧
      (Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ) ∧
      (∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] = v i * (1 - v i)) ∧
      0 < trueProportionPV 0.9 0.9 0.5 ∧ trueProportionPV 0.9 0.9 0.5 < 1 ∧
      0 < trueProportionPV 0.9 0.9 0.3 ∧ trueProportionPV 0.9 0.9 0.3 < 1 ∧
      IsAsymptoticallyLinear
          (fun n ω ↦ logORPV (θhat 0 n ω) (θhat 1 n ω) (θhat 2 n ω) (θhat 3 n ω)
            (θhat 4 n ω) (θhat 5 n ω))
          (logORPV 0.9 0.9 0.5 0.9 0.9 0.3)
          (fun x ↦ ∑ i, marshallGrad 0.9 0.9 0.5 0.9 0.9 0.3 i * φ i x) O μ ∧
        μ[fun ω ↦ (∑ i, marshallGrad 0.9 0.9 0.5 0.9 0.9 0.3 i * φ i (O 0 ω)) ^ 2] =
          marshallA (0.9 * (1 - 0.9)) (0.9 * (1 - 0.9)) (0.3 * (1 - 0.3)) 0.9 0.9 0.3 /
              (trueProportionPV 0.9 0.9 0.3 * (1 - trueProportionPV 0.9 0.9 0.3)) ^ 2 +
            marshallA (0.9 * (1 - 0.9)) (0.9 * (1 - 0.9)) (0.5 * (1 - 0.5)) 0.9 0.9 0.5 /
              (trueProportionPV 0.9 0.9 0.5 * (1 - trueProportionPV 0.9 0.9 0.5)) ^ 2 := by
  intro μ v O θhat φ
  obtain ⟨hO, hAL, hind, hσ'⟩ := oneSample_hypotheses marshallQ v
    fun i ↦ by fin_cases i <;> rfl
  have hσ : ∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] = ![0.9 * (1 - 0.9), 0.9 * (1 - 0.9),
      0.5 * (1 - 0.5), 0.9 * (1 - 0.9), 0.9 * (1 - 0.9), 0.3 * (1 - 0.3)] i := by
    intro i
    rw [hσ' i]
    fin_cases i <;> rfl
  have hP : 0 < trueProportionPV 0.9 0.9 0.5 ∧ trueProportionPV 0.9 0.9 0.5 < 1 ∧
      0 < trueProportionPV 0.9 0.9 0.3 ∧ trueProportionPV 0.9 0.9 0.3 < 1 := by
    norm_num [trueProportionPV]
  obtain ⟨h1, h2, h3, h4⟩ := hP
  have hv : (![0.9, 0.9, 0.5, 0.9, 0.9, 0.3] : Fin 6 → ℝ) = v := rfl
  exact ⟨hO, hAL, hind, hσ', h1, h2, h3, h4, marshall_asymptotic hO (θhat := θhat)
    (by rw [hv]; exact hAL) hind hσ h1 h2 h3 h4⟩

/-- **`ivPooled_asymptotic` holds for a real sampling scheme**: two independent coins per
observation with success probabilities `0.5` and `0.3`, the two sample proportions pooled with the
inverse of their binomial variances `0.25` and `0.21`. -/
theorem ivPooled_asymptotic_instance :
    let μ := gridMeasure fun (_ : ℕ) b ↦ (![pt 0.5, pt 0.3] : Fin 2 → I) b
    let v : Fin 2 → ℝ := ![0.5, 0.3]
    let V : Fin 2 → ℝ := ![0.5 * (1 - 0.5), 0.3 * (1 - 0.3)]
    let O : ℕ → (ℕ → Fin 2 → Bool) → Fin 2 → Bool := fun j ω ↦ ω j
    let θhat : Fin 2 → ℕ → (ℕ → Fin 2 → Bool) → ℝ := fun i ↦ sampleMean (fun x ↦ coin (x i)) O
    let φ : Fin 2 → (Fin 2 → Bool) → ℝ := fun i x ↦ coin (x i) - v i
    IsIIDSample O μ ∧ (∀ i, IsAsymptoticallyLinear (θhat i) (v i) (φ i) O μ) ∧
      (Pairwise fun i j ↦ IndepFun (fun ω ↦ φ i (O 0 ω)) (fun ω ↦ φ j (O 0 ω)) μ) ∧
      (∀ i, 0 < V i) ∧ (∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] = V i) ∧
      IsAsymptoticallyLinear (fun n ω ↦ ivPooled (fun i ↦ θhat i n ω) V) (ivPooled v V)
          (fun x ↦ ∑ i, (1 / V i) / ivTotalWeight V * φ i x) O μ ∧
        μ[fun ω ↦ (∑ i, (1 / V i) / ivTotalWeight V * φ i (O 0 ω)) ^ 2] =
          ivPooledVariance V := by
  intro μ v V O θhat φ
  obtain ⟨hO, hAL, hind, hσ'⟩ := oneSample_hypotheses ![pt 0.5, pt 0.3] v
    fun i ↦ by fin_cases i <;> rfl
  have hV : ∀ i, 0 < V i := fun i ↦ by fin_cases i <;> norm_num [V]
  have hσ : ∀ i, μ[fun ω ↦ φ i (O 0 ω) ^ 2] = V i := fun i ↦ by
    rw [hσ' i]
    fin_cases i <;> rfl
  exact ⟨hO, hAL, hind, hV, hσ, ivPooled_asymptotic (by norm_num) hO hAL hind hV hσ⟩

/-! ### The theorems for independent studies of different sizes -/

/-- The hypotheses shared by the several-sample instances: the rows of a grid of independent
coins, with success probability `q i` in row `i`, are mutually independent i.i.d. samples, and the
indicator of success has mean `q i` in row `i`. -/
theorem rows_hypotheses {k : ℕ} (q : Fin k → I) (v : Fin k → ℝ) (hv : ∀ i, (q i : ℝ) = v i) :
    (∀ i, IsIIDSample (fun j (ω : Fin k → ℕ → Bool) ↦ ω i j) (gridMeasure fun a (_ : ℕ) ↦ q a)) ∧
      iIndepFun (fun i (ω : Fin k → ℕ → Bool) ↦ fun j ↦ ω i j) (gridMeasure fun a (_ : ℕ) ↦ q a) ∧
      ∀ i, ∫ ω, coin (ω i 0) ∂(gridMeasure fun a (_ : ℕ) ↦ q a) = v i :=
  ⟨gridMeasure_rows_isIIDSample q, gridMeasure_iIndepFun_rows _,
    fun i ↦ (gridMeasure_integral_coin _ i 0).trans (hv i)⟩

/-- **`greenland_nondifferential_of_sizes` holds for a real sampling scheme.** Four independent
studies of coins: a validation study of `2n` truly exposed subjects (each classified exposed with
probability `SE = 0.9`), one of `3n` truly unexposed subjects (classified unexposed with
probability `SP = 0.9`), `n` cases (observed exposed with probability `pe₁ = 0.5`) and `4n`
controls (`pe₀ = 0.3`). With the sample proportions as estimators, `√n` times the error of the
adjusted log odds ratio converges in distribution to the centered Gaussian with the printed
Greenland variance at the binomial input variances and the limit ratios `(2, 3, 1, 4)`, and `n`
times the printed variance at the actual sizes converges to it. -/
theorem greenland_nondifferential_of_sizes_instance :
    let μ := gridMeasure fun a (_ : ℕ) ↦ (![pt 0.9, pt 0.9, pt 0.5, pt 0.3] : Fin 4 → I) a
    let c : Fin 4 → ℕ := ![2, 3, 1, 4]
    let phat : Fin 4 → ℕ → (Fin 4 → ℕ → Bool) → ℝ := fun i n ↦
      sampleMean coin (fun j ω ↦ ω i j) (c i * n)
    let V : ℝ := greenlandNondiff (0.9 * (1 - 0.9) / 2) (0.9 * (1 - 0.9) / 3) 0.9 0.9 0.5 1 0.3 4
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
        (logORSeSp (phat 0 n ω) (phat 1 n ω) (phat 2 n ω) (phat 0 n ω) (phat 1 n ω) (phat 3 n ω) -
          logORSeSp 0.9 0.9 0.5 0.9 0.9 0.3)) atTop id (fun _ ↦ μ)
        (gaussianReal 0 V.toNNReal) ∧
      Tendsto (fun n : ℕ ↦ (n : ℝ) * greenlandNondiff (0.9 * (1 - 0.9) / (c 0 * n : ℕ))
          (0.9 * (1 - 0.9) / (c 1 * n : ℕ)) 0.9 0.9 0.5 (c 2 * n : ℕ) 0.3 (c 3 * n : ℕ))
        atTop (𝓝 V) := by
  intro μ c phat V
  obtain ⟨hO, hind, hp⟩ := rows_hypotheses ![pt 0.9, pt 0.9, pt 0.5, pt 0.3] ![0.9, 0.9, 0.5, 0.3]
    fun i ↦ by fin_cases i <;> rfl
  have hN : ∀ i, Tendsto (fun n ↦ ((c i * n : ℕ) : ℝ) / n) atTop (𝓝 (![2, 3, 1, 4] i)) := by
    intro i
    have := tendsto_natCast_mul_div (c i)
    fin_cases i <;> simpa [c] using this
  have hVeq : greenlandNondiff (0.9 * (1 - 0.9) / (![2, 3, 1, 4] : Fin 4 → ℝ) 0)
      (0.9 * (1 - 0.9) / (![2, 3, 1, 4] : Fin 4 → ℝ) 1) 0.9 0.9 0.5
      ((![2, 3, 1, 4] : Fin 4 → ℝ) 2) 0.3 ((![2, 3, 1, 4] : Fin 4 → ℝ) 3) = V := by
    simp only [V]
    norm_num
  have := greenland_nondifferential_of_sizes (f := fun _ ↦ coin) hO hind (fun _ ↦ measurable_coin)
    (fun _ ↦ coin_mem) hp (N := fun i n ↦ c i * n) (r := ![2, 3, 1, 4])
    (fun i ↦ by fin_cases i <;> norm_num) hN (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Y := id) (P' := gaussianReal 0 V.toNNReal) (by rw [hVeq]; exact HasLaw.id)
  rw [hVeq] at this
  exact this

/-- **`greenland_differential_of_sizes` holds for a real sampling scheme.** Six independent studies
of coins: validation studies among cases of sizes `2n` (sensitivity `0.9`) and `3n` (specificity
`0.9`), `n` cases (`pe₁ = 0.5`), validation studies among controls of sizes `2n` (sensitivity
`0.8`) and `3n` (specificity `0.9`), and `4n` controls (`pe₀ = 0.3`). -/
theorem greenland_differential_of_sizes_instance :
    let μ := gridMeasure fun a (_ : ℕ) ↦
      (![pt 0.9, pt 0.9, pt 0.5, pt 0.8, pt 0.9, pt 0.3] : Fin 6 → I) a
    let c : Fin 6 → ℕ := ![2, 3, 1, 2, 3, 4]
    let phat : Fin 6 → ℕ → (Fin 6 → ℕ → Bool) → ℝ := fun i n ↦
      sampleMean coin (fun j ω ↦ ω i j) (c i * n)
    let V : ℝ := greenlandTerm (0.9 * (1 - 0.9) / 2) (0.9 * (1 - 0.9) / 3) 0.9 0.9 0.5 1 +
      greenlandTerm (0.8 * (1 - 0.8) / 2) (0.9 * (1 - 0.9) / 3) 0.8 0.9 0.3 4
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
        (logORSeSp (phat 0 n ω) (phat 1 n ω) (phat 2 n ω) (phat 3 n ω) (phat 4 n ω)
          (phat 5 n ω) - logORSeSp 0.9 0.9 0.5 0.8 0.9 0.3)) atTop id (fun _ ↦ μ)
        (gaussianReal 0 V.toNNReal) ∧
      Tendsto (fun n : ℕ ↦ (n : ℝ) *
          (greenlandTerm (0.9 * (1 - 0.9) / (c 0 * n : ℕ)) (0.9 * (1 - 0.9) / (c 1 * n : ℕ))
              0.9 0.9 0.5 (c 2 * n : ℕ) +
            greenlandTerm (0.8 * (1 - 0.8) / (c 3 * n : ℕ)) (0.9 * (1 - 0.9) / (c 4 * n : ℕ))
              0.8 0.9 0.3 (c 5 * n : ℕ))) atTop (𝓝 V) := by
  intro μ c phat V
  obtain ⟨hO, hind, hp⟩ := rows_hypotheses ![pt 0.9, pt 0.9, pt 0.5, pt 0.8, pt 0.9, pt 0.3]
    ![0.9, 0.9, 0.5, 0.8, 0.9, 0.3] fun i ↦ by fin_cases i <;> rfl
  have hN : ∀ i, Tendsto (fun n ↦ ((c i * n : ℕ) : ℝ) / n) atTop
      (𝓝 (![2, 3, 1, 2, 3, 4] i)) := by
    intro i
    have := tendsto_natCast_mul_div (c i)
    fin_cases i <;> simpa [c] using this
  have hVeq : greenlandTerm (0.9 * (1 - 0.9) / (![2, 3, 1, 2, 3, 4] : Fin 6 → ℝ) 0)
        (0.9 * (1 - 0.9) / (![2, 3, 1, 2, 3, 4] : Fin 6 → ℝ) 1) 0.9 0.9 0.5
        ((![2, 3, 1, 2, 3, 4] : Fin 6 → ℝ) 2) +
      greenlandTerm (0.8 * (1 - 0.8) / (![2, 3, 1, 2, 3, 4] : Fin 6 → ℝ) 3)
        (0.9 * (1 - 0.9) / (![2, 3, 1, 2, 3, 4] : Fin 6 → ℝ) 4) 0.8 0.9 0.3
        ((![2, 3, 1, 2, 3, 4] : Fin 6 → ℝ) 5) = V := by
    simp only [V]
    norm_num
  have := greenland_differential_of_sizes (f := fun _ ↦ coin) hO hind (fun _ ↦ measurable_coin)
    (fun _ ↦ coin_mem) hp (N := fun i n ↦ c i * n) (r := ![2, 3, 1, 2, 3, 4])
    (fun i ↦ by fin_cases i <;> norm_num) hN (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Y := id) (P' := gaussianReal 0 V.toNNReal) (by rw [hVeq]; exact HasLaw.id)
  rw [hVeq] at this
  exact this

/-- **`marshall_of_sizes` holds for a real sampling scheme.** Six independent studies of coins:
validation samples of `2n` cases classified exposed (truly exposed with probability
`PPV₁ = 0.9`) and `2n` classified unexposed (`NPV₁ = 0.9`), `n` cases (`pe₁ = 0.5`), validation
samples of `3n` controls classified exposed (`PPV₀ = 0.9`) and `3n` classified unexposed
(`NPV₀ = 0.9`), and `4n` controls (`pe₀ = 0.3`). -/
theorem marshall_of_sizes_instance :
    let μ := gridMeasure fun a (_ : ℕ) ↦
      (![pt 0.9, pt 0.9, pt 0.5, pt 0.9, pt 0.9, pt 0.3] : Fin 6 → I) a
    let c : Fin 6 → ℕ := ![2, 2, 1, 3, 3, 4]
    let phat : Fin 6 → ℕ → (Fin 6 → ℕ → Bool) → ℝ := fun i n ↦
      sampleMean coin (fun j ω ↦ ω i j) (c i * n)
    let V : ℝ :=
      marshallA (0.9 * (1 - 0.9) / 3) (0.9 * (1 - 0.9) / 3) (0.3 * (1 - 0.3) / 4) 0.9 0.9 0.3 /
          (trueProportionPV 0.9 0.9 0.3 * (1 - trueProportionPV 0.9 0.9 0.3)) ^ 2 +
        marshallA (0.9 * (1 - 0.9) / 2) (0.9 * (1 - 0.9) / 2) (0.5 * (1 - 0.5) / 1) 0.9 0.9 0.5 /
          (trueProportionPV 0.9 0.9 0.5 * (1 - trueProportionPV 0.9 0.9 0.5)) ^ 2
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
        (logORPV (phat 0 n ω) (phat 1 n ω) (phat 2 n ω) (phat 3 n ω) (phat 4 n ω)
          (phat 5 n ω) - logORPV 0.9 0.9 0.5 0.9 0.9 0.3)) atTop id (fun _ ↦ μ)
        (gaussianReal 0 V.toNNReal) := by
  intro μ c phat V
  obtain ⟨hO, hind, hp⟩ := rows_hypotheses ![pt 0.9, pt 0.9, pt 0.5, pt 0.9, pt 0.9, pt 0.3]
    ![0.9, 0.9, 0.5, 0.9, 0.9, 0.3] fun i ↦ by fin_cases i <;> rfl
  have hN : ∀ i, Tendsto (fun n ↦ ((c i * n : ℕ) : ℝ) / n) atTop
      (𝓝 (![2, 2, 1, 3, 3, 4] i)) := by
    intro i
    have := tendsto_natCast_mul_div (c i)
    fin_cases i <;> simpa [c] using this
  have hVeq :
      marshallA (0.9 * (1 - 0.9) / (![2, 2, 1, 3, 3, 4] : Fin 6 → ℝ) 3)
          (0.9 * (1 - 0.9) / (![2, 2, 1, 3, 3, 4] : Fin 6 → ℝ) 4)
          (0.3 * (1 - 0.3) / (![2, 2, 1, 3, 3, 4] : Fin 6 → ℝ) 5) 0.9 0.9 0.3 /
          (trueProportionPV 0.9 0.9 0.3 * (1 - trueProportionPV 0.9 0.9 0.3)) ^ 2 +
        marshallA (0.9 * (1 - 0.9) / (![2, 2, 1, 3, 3, 4] : Fin 6 → ℝ) 0)
          (0.9 * (1 - 0.9) / (![2, 2, 1, 3, 3, 4] : Fin 6 → ℝ) 1)
          (0.5 * (1 - 0.5) / (![2, 2, 1, 3, 3, 4] : Fin 6 → ℝ) 2) 0.9 0.9 0.5 /
          (trueProportionPV 0.9 0.9 0.5 * (1 - trueProportionPV 0.9 0.9 0.5)) ^ 2 = V := by
    simp only [V]
    norm_num
  have := marshall_of_sizes (f := fun _ ↦ coin) hO hind (fun _ ↦ measurable_coin)
    (fun _ ↦ coin_mem) hp (N := fun i n ↦ c i * n) (r := ![2, 2, 1, 3, 3, 4])
    (fun i ↦ by fin_cases i <;> norm_num) hN (by norm_num [trueProportionPV])
    (by norm_num [trueProportionPV]) (by norm_num [trueProportionPV])
    (by norm_num [trueProportionPV]) (Y := id) (P' := gaussianReal 0 V.toNNReal)
    (by rw [hVeq]; exact HasLaw.id)
  exact this.1

/-- The pooled estimate is a measurable function of the estimates and the variances. -/
theorem measurable_ivPooled {k : ℕ} :
    Measurable fun x : (Fin k → ℝ) × (Fin k → ℝ) ↦ ivPooled x.1 x.2 := by
  unfold ivPooled ivTotalWeight
  fun_prop

/-- The sample proportion of a row of the grid is a measurable function of the grid. -/
theorem measurable_sampleMean_row {k : ℕ} (i : Fin k) (m : ℕ) :
    Measurable fun ω : Fin k → ℕ → Bool ↦ sampleMean coin (fun j ω ↦ ω i j) m ω := by
  unfold sampleMean
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ ↦ ?_)
  exact measurable_coin.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))

/-- **`ivPooled_of_sizes` holds for a real sampling scheme.** Two independent studies of coins,
of sizes `n` (success probability `0.5`) and `2n` (`0.3`), pooled with the limiting weights
`Vᵢ = pᵢ (1 - pᵢ) / rᵢ`. -/
theorem ivPooled_of_sizes_instance :
    let μ := gridMeasure fun a (_ : ℕ) ↦ (![pt 0.5, pt 0.3] : Fin 2 → I) a
    let c : Fin 2 → ℕ := ![1, 2]
    let v : Fin 2 → ℝ := ![0.5, 0.3]
    let σ2 : Fin 2 → ℝ := fun i ↦ v i * (1 - v i)
    let phat : Fin 2 → ℕ → (Fin 2 → ℕ → Bool) → ℝ := fun i ↦ sampleMean coin (fun j ω ↦ ω i j)
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
        (ivPooled (fun i ↦ phat i (c i * n) ω) (fun i ↦ σ2 i / c i) -
          ivPooled v fun i ↦ σ2 i / c i)) atTop id (fun _ ↦ μ)
        (gaussianReal 0 (ivPooledVariance fun i ↦ σ2 i / c i).toNNReal) ∧
      Tendsto (fun n : ℕ ↦ (n : ℝ) * ivPooledVariance fun i ↦ σ2 i / (c i * n : ℕ)) atTop
        (𝓝 (ivPooledVariance fun i ↦ σ2 i / c i)) := by
  intro μ c v σ2 phat
  obtain ⟨hO, hind, hp⟩ := rows_hypotheses ![pt 0.5, pt 0.3] v fun i ↦ by fin_cases i <;> rfl
  have hAL : ∀ i, _ := fun i ↦
    sampleProportion_isAsymptoticallyLinear (hO i) measurable_coin coin_mem (hp i)
  exact ivPooled_of_sizes (by norm_num) hO hind (fun i ↦ (hAL i).1)
    (fun i ↦ by fin_cases i <;> norm_num [σ2, v]) (fun i ↦ (hAL i).2)
    (N := fun i n ↦ c i * n) (fun i ↦ by fin_cases i <;> norm_num [c])
    (fun i ↦ tendsto_natCast_mul_div (c i))
    (fun n ↦ measurable_ivPooled.comp_aemeasurable
      ((AEMeasurable.of_eval fun i ↦ (measurable_sampleMean_row i _).aemeasurable).prodMk
        aemeasurable_const)) HasLaw.id

/-- A sequence converging in probability, mapped by a continuous function and multiplied by a
convergent deterministic sequence, converges in probability to the corresponding limit. -/
theorem tendstoInMeasure_comp_mul_of_tendsto {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} {a : ℝ} (hX : TendstoInMeasure μ X atTop fun _ ↦ a)
    {g : ℝ → ℝ} (hg : Continuous g) {c : ℕ → ℝ} {b : ℝ} (hc : Tendsto c atTop (𝓝 b)) :
    TendstoInMeasure μ (fun n ω ↦ g (X n ω) * c n) atTop fun _ ↦ g a * b := by
  have hc' : TendstoInMeasure μ (fun n (_ : Ω) ↦ c n) atTop fun _ ↦ b := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    refine tendsto_const_nhds.congr' ?_
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hc).eventually (gt_mem_nhds hε)
    filter_upwards [this] with n hn
    have : {ω : Ω | ε ≤ ‖c n - b‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hn
    rw [this, measure_empty]
  have h := tendstoInMeasure_pi_comp (X := ![X, fun n _ ↦ c n]) (θ := ![a, b])
    (fun i ↦ by fin_cases i; exacts [hX, hc'])
    (ρ := fun x ↦ g (x 0) * x 1)
    ((hg.comp (continuous_apply 0)).mul (continuous_apply 1)).continuousAt
  simpa using h

/-- **`ivPooled_estimated_of_sizes` holds for a real sampling scheme, with the printed weights.**
Two independent studies of coins with the common success probability `θ₀ = 0.5`, of sizes `n` and
`2n`. The weights are the inverses of the printed variance estimates `p̂ᵢ (1 - p̂ᵢ) / Nᵢ`, scaled
by `n` (which does not change the pooled estimate, `ivPooled_smul`): these are consistent for
`Vᵢ = θ₀ (1 - θ₀) / rᵢ`, and the pooled estimate has the asymptotic variance of the known
weights, `ivPooledVariance V`. -/
theorem ivPooled_estimated_of_sizes_instance :
    let μ := gridMeasure fun a (_ : ℕ) ↦ (![pt 0.5, pt 0.5] : Fin 2 → I) a
    let c : Fin 2 → ℕ := ![1, 2]
    let phat : Fin 2 → ℕ → (Fin 2 → ℕ → Bool) → ℝ := fun i n ↦
      sampleMean coin (fun j ω ↦ ω i j) (c i * n)
    let Vhat : Fin 2 → ℕ → (Fin 2 → ℕ → Bool) → ℝ := fun i n ω ↦
      phat i n ω * (1 - phat i n ω) * ((n : ℝ) / (c i * n : ℕ))
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) *
        (ivPooled (fun i ↦ phat i n ω) (fun i ↦ Vhat i n ω) - 0.5)) atTop id (fun _ ↦ μ)
        (gaussianReal 0 (ivPooledVariance fun i ↦ 0.5 * (1 - 0.5) / c i).toNNReal) ∧
      ∀ n ω, n ≠ 0 → ivPooled (fun i ↦ phat i n ω) (fun i ↦ Vhat i n ω) =
        ivPooled (fun i ↦ phat i n ω) fun i ↦ phat i n ω * (1 - phat i n ω) / (c i * n : ℕ) := by
  intro μ c phat Vhat
  obtain ⟨hO, hind, hp⟩ := rows_hypotheses ![pt 0.5, pt 0.5] (fun _ ↦ 0.5)
    fun i ↦ by fin_cases i <;> rfl
  have hAL : ∀ i, _ := fun i ↦
    sampleProportion_isAsymptoticallyLinear (hO i) measurable_coin coin_mem (hp i)
  have hr : ∀ i, (0 : ℝ) < c i := fun i ↦ by fin_cases i <;> norm_num [c]
  have hN : ∀ i, Tendsto (fun n ↦ ((c i * n : ℕ) : ℝ) / n) atTop (𝓝 (c i : ℝ)) :=
    fun i ↦ tendsto_natCast_mul_div (c i)
  have hVhat : ∀ i, TendstoInMeasure μ (Vhat i) atTop fun _ ↦ 0.5 * (1 - 0.5) / c i := by
    intro i
    have hcons := ((hAL i).1.isConsistent (hO i)).comp_tendsto
      (tendsto_atTop_of_div_tendsto (hr i) (hN i))
    have hinv : Tendsto (fun n : ℕ ↦ (n : ℝ) / (c i * n : ℕ)) atTop (𝓝 (c i : ℝ)⁻¹) :=
      ((hN i).inv₀ (hr i).ne').congr fun n ↦ inv_div _ _
    have := tendstoInMeasure_comp_mul_of_tendsto hcons
      (g := fun x ↦ x * (1 - x)) (by fun_prop) hinv
    rw [div_eq_mul_inv]
    exact this
  have hmeasθ : ∀ n, AEMeasurable (fun ω ↦ (fun i ↦ phat i n ω)) μ := fun n ↦
    AEMeasurable.of_eval fun i ↦ (measurable_sampleMean_row i _).aemeasurable
  refine ⟨ivPooled_estimated_of_sizes (by norm_num) hO hind (fun i ↦ (hAL i).1)
    (σ2 := fun _ ↦ 0.5 * (1 - 0.5)) (fun _ ↦ by norm_num) (fun i ↦ (hAL i).2)
    (N := fun i n ↦ c i * n) hr hN hVhat
    (fun n ↦ measurable_ivPooled.comp_aemeasurable ((hmeasθ n).prodMk aemeasurable_const))
    (fun n ↦ measurable_ivPooled.comp_aemeasurable ((hmeasθ n).prodMk
      (AEMeasurable.of_eval fun i ↦ (((measurable_sampleMean_row i _).mul
        (measurable_const.sub (measurable_sampleMean_row i _))).mul_const _).aemeasurable)))
    HasLaw.id, fun n ω hn ↦ ?_⟩
  have : (fun i ↦ Vhat i n ω) =
      (n : ℝ) • fun i ↦ phat i n ω * (1 - phat i n ω) / (c i * n : ℕ) := by
    funext i
    simp only [Vhat, Pi.smul_apply, smul_eq_mul]
    ring
  rw [this]
  exact (ivPooled_smul _ _ (Nat.cast_ne_zero.2 hn)).1

end BiasAnalysis.SamplingWitnesses

end CausalInference
